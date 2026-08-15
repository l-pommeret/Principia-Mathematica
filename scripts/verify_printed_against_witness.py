#!/usr/bin/env python3
"""Compare PM-VERBATIM readings with the repository's Gutenberg witnesses.

This gate checks text, not Lean meaning.  It deliberately has no fuzzy matching:
blocks and witness readings meet only through their exact PM proposition ID, and
the two readings are then reduced by the explicit, reviewable rules below.

Unsupported notation is audit debt, never evidence of agreement.  In particular
the gate names fractions used to display substitutions, TeX arrays/aligned
environments, multiline ``Dem.`` blocks, unknown TeX commands, missing witnesses,
and genuinely ambiguous duplicate witness readings.  Such blocks are reported
but do not by themselves fail CI; divergences and invalid exemptions do.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
import textwrap
import unicodedata
from collections import defaultdict
from dataclasses import dataclass
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_WITNESSES = {
    "PM1": Path("metadata/witnesses/gutenberg/pg78050-tex.txt"),
    "PM2": Path("metadata/witnesses/gutenberg/pg78255-tex.txt"),
}
DEFAULT_EXEMPTIONS = Path("metadata/printed_witness_exemptions.json")
MIN_REASON_LENGTH = 40

BLOCK_RE = re.compile(
    r"PM-VERBATIM-BEGIN\s+(\S+)\s*\n(.*?)\n"
    r"PM-VERBATIM-END\s+(\S+)",
    re.DOTALL,
)
WITNESS_RE = re.compile(r"^\*(\d+(?:·\d+)+)\.\s*(\S.*?)\s*$", re.MULTILINE)
PROPOSITION_RE = re.compile(r"^(PM\d+):✱(\d+(?:·\d+)+)$")


@dataclass(frozen=True)
class TexRule:
    token: str
    replacement: str
    rationale: str


# This is the normative TeX -> diplomatic Unicode table.  Every entry carries
# the editorial rule it implements so a reviewer can contest one mapping without
# reverse-engineering a general-purpose TeX renderer.  Command matching observes
# TeX command boundaries: e.g. ``\in`` cannot consume the start of ``\infty``.
TEX_RULES = (
    TexRule(r"\vdash", "⊢", "PM's assertion sign is represented by U+22A2."),
    TexRule(r"\sim", "∼", "Logical negation is represented by U+223C."),
    TexRule(r"\equiv", "≡", "Logical equivalence is represented by U+2261."),
    TexRule(r"\lor", "∨", "Logical disjunction is represented by U+2228."),
    TexRule(r"\supset", "⊃", "Material implication is represented by U+2283."),
    TexRule(r"\in", "∈", "Class membership is represented by U+2208."),
    TexRule(r"\ni", "∋", "Reverse membership is represented by U+220B."),
    TexRule(r"\notin", "∉", "Negated membership is represented by U+2209."),
    TexRule(r"\subset", "⊂", "PM's class inclusion sign is represented by U+2282."),
    TexRule(r"\supseteq", "⊇", "Non-strict reverse inclusion is represented by U+2287."),
    TexRule(r"\subseteq", "⊆", "Non-strict inclusion is represented by U+2286."),
    TexRule(r"\cap", "∩", "Class intersection is represented by U+2229."),
    TexRule(r"\cup", "∪", "Class union is represented by U+222A."),
    TexRule(r"\neq", "≠", "Inequality is represented by U+2260."),
    TexRule(r"\leq", "≤", "Non-strict order is represented by U+2264."),
    TexRule(r"\geq", "≥", "Non-strict reverse order is represented by U+2265."),
    TexRule(r"\exists", "∃", "Existential quantification is represented by U+2203."),
    TexRule(r"\forall", "∀", "Universal quantification is represented by U+2200."),
    TexRule(r"\rightarrow", "→", "A right arrow is represented by U+2192."),
    TexRule(r"\leftarrow", "←", "A left arrow is represented by U+2190."),
    TexRule(r"\leftrightarrow", "↔", "A two-way arrow is represented by U+2194."),
    TexRule(r"\Lambda", "Λ", "The uppercase Greek lambda is represented literally."),
    TexRule(r"\alpha", "α", "The lowercase Greek alpha is represented literally."),
    TexRule(r"\beta", "β", "The lowercase Greek beta is represented literally."),
    TexRule(r"\gamma", "γ", "The lowercase Greek gamma is represented literally."),
    TexRule(r"\delta", "δ", "The lowercase Greek delta is represented literally."),
    TexRule(r"\epsilon", "ε", "The lowercase Greek epsilon is represented literally."),
    TexRule(r"\varepsilon", "ε", "Both epsilon TeX variants share PM's glyph here."),
    TexRule(r"\zeta", "ζ", "The lowercase Greek zeta is represented literally."),
    TexRule(r"\eta", "η", "The lowercase Greek eta is represented literally."),
    TexRule(r"\theta", "θ", "The lowercase Greek theta is represented literally."),
    TexRule(r"\iota", "ι", "The lowercase Greek iota is represented literally."),
    TexRule(r"\kappa", "κ", "The lowercase Greek kappa is represented literally."),
    TexRule(r"\lambda", "λ", "The lowercase Greek lambda is represented literally."),
    TexRule(r"\mu", "μ", "The lowercase Greek mu is represented literally."),
    TexRule(r"\nu", "ν", "The lowercase Greek nu is represented literally."),
    TexRule(r"\xi", "ξ", "The lowercase Greek xi is represented literally."),
    TexRule(r"\pi", "π", "The lowercase Greek pi is represented literally."),
    TexRule(r"\rho", "ρ", "The lowercase Greek rho is represented literally."),
    TexRule(r"\sigma", "σ", "The lowercase Greek sigma is represented literally."),
    TexRule(r"\tau", "τ", "The lowercase Greek tau is represented literally."),
    TexRule(r"\phi", "φ", "The lowercase Greek phi is represented literally."),
    TexRule(r"\varphi", "φ", "Both phi TeX variants share PM's glyph here."),
    TexRule(r"\chi", "χ", "The lowercase Greek chi is represented literally."),
    TexRule(r"\psi", "ψ", "The lowercase Greek psi is represented literally."),
    TexRule(r"\omega", "ω", "The lowercase Greek omega is represented literally."),
    TexRule(r"\colon", ":", "TeX's relation colon is PM's printed colon."),
    TexRule(r"\ldotp", ".", "TeX's low dot is PM's printed full stop."),
    TexRule(r"\vert", "|", "A vertical bar is represented by ASCII vertical bar."),
    TexRule(r"\mid", "|", "A relation bar is represented by the same visible bar."),
    TexRule(r"\ast", "✱", "A referenced PM star is represented by U+2731."),
    TexRule(r"\quad", " ", "A quad carries spacing only; semantic spaces are collapsed."),
    TexRule(r"\qquad", " ", "A double quad carries spacing only."),
    TexRule(r"\,", " ", "A TeX thin space carries no textual content."),
    TexRule(r"\;", " ", "A TeX thick space carries no textual content."),
    TexRule(r"\:", " ", "A TeX medium space carries no textual content."),
    TexRule(r"\!", " ", "A negative thin space carries no textual content."),
)


class UnsupportedNormalization(ValueError):
    """A reading uses syntax for which this gate has no declared rule."""


class RegistryError(ValueError):
    """The exemption registry is malformed, incomplete, or stale."""


@dataclass(frozen=True)
class Block:
    proposition: str
    reading: str
    path: Path
    line: int


@dataclass(frozen=True)
class Exemption:
    proposition: str
    gutenberg_reading: str
    repository_reading: str
    reason: str


@dataclass(frozen=True)
class Divergence:
    block: Block
    gutenberg_reading: str


@dataclass(frozen=True)
class UnsupportedBlock:
    block: Block
    reason: str


@dataclass
class Report:
    examined: int = 0
    compared: int = 0
    conforming: int = 0
    exempted: int = 0
    divergences: list[Divergence] | None = None
    unsupported: list[UnsupportedBlock] | None = None
    registry_errors: list[str] | None = None

    def __post_init__(self) -> None:
        self.divergences = [] if self.divergences is None else self.divergences
        self.unsupported = [] if self.unsupported is None else self.unsupported
        self.registry_errors = [] if self.registry_errors is None else self.registry_errors


def _replace_command(text: str, token: str, replacement: str) -> str:
    if token in {r"\,", r"\;", r"\:", r"\!"}:
        return text.replace(token, replacement)
    command = re.escape(token) + r"(?![A-Za-z])"
    return re.sub(command, lambda _match: replacement, text)


def _unwrap_text_commands(text: str) -> str:
    """Apply the explicit ``\text{…} -> …`` rule without parsing arbitrary TeX."""
    pattern = re.compile(r"\\text\{([^{}]*)\}")
    previous = None
    while previous != text:
        previous = text
        text = pattern.sub(lambda match: match.group(1), text)
    if r"\text" in text:
        raise UnsupportedNormalization("commande \\text imbriquée ou sans accolade simple")
    return text


def normalize_reading(reading: str, *, tex: bool) -> str:
    r"""Return one canonical string or explicitly refuse unsupported notation.

    Besides ``TEX_RULES``, the deterministic editorial rules are:

    * Unicode is NFC-normalized; typographic minus/apostrophe variants used by
      the two transcriptions are folded to one diplomatic code point.
    * outer TeX math delimiters and size-only ``\left``/``\right`` commands do
      not contribute a printed character;
    * ``\text{plain text}`` contributes its literal contents;
    * TeX grouping braces are removed, while escaped printed braces survive;
    * an ASCII star immediately before a PM number becomes ``✱``;
    * all whitespace is removed, but every PM dot, colon and bracket remains.
      Thus spacing changes cannot hide a changed negation or connective.
    """
    text = unicodedata.normalize("NFC", reading.strip())
    if tex:
        if r"\frac" in text:
            raise UnsupportedNormalization("fraction de substitution TeX (\\frac)")
        if r"\begin" in text or r"\end" in text or r"\\" in text:
            raise UnsupportedNormalization("environnement TeX array/aligned ou saut de ligne")
        if "_" in text or "^" in text:
            raise UnsupportedNormalization(
                "indice ou exposant TeX sans règle diplomatique déclarée"
            )

        # Math-mode wrappers describe the transcription, not printed symbols.
        text = re.sub(r"^\\\(|\\\)$", "", text.strip())
        text = re.sub(r"^\\\[|\\\]$", "", text.strip())
        text = _replace_command(text, r"\left", "")
        text = _replace_command(text, r"\right", "")
        text = _unwrap_text_commands(text)

        literal_left = "\uE000"
        literal_right = "\uE001"
        text = text.replace(r"\{", literal_left).replace(r"\}", literal_right)
        for rule in TEX_RULES:
            text = _replace_command(text, rule.token, rule.replacement)
        text = text.replace("{", "").replace("}", "")
        text = text.replace(literal_left, "{").replace(literal_right, "}")

        unknown = sorted(set(re.findall(r"\\[A-Za-z]+|\\.", text)))
        if unknown:
            raise UnsupportedNormalization(
                "commande TeX sans règle explicite: " + ", ".join(unknown)
            )

    # These are documented diplomatic equivalences, applied symmetrically.
    #
    # ∈ folds to ε because the 1910 edition sets class membership with a Greek
    # epsilon, while the Gutenberg transcription modernises it to U+2208.  The
    # repository follows the printed page, so the two readings say the same
    # thing in two alphabets, and 15 blocks diverged on nothing else.  PM uses
    # ε for membership and for no other purpose, so folding the pair cannot
    # merge two distinct signs; and being a fold, it can only make readings
    # agree that already agreed elsewhere -- it cannot turn a passing block
    # into a failing one.
    text = text.translate(
        str.maketrans(
            {
                "−": "-",
                "–": "-",
                "‘": "ʻ",
                "’": "ʻ",
                "′": "ʻ",
                "∈": "ε",
            }
        )
    )
    text = re.sub(r"\*(?=\d)", "✱", text)
    return re.sub(r"\s+", "", text)


def _proposition_parts(proposition: str) -> tuple[str, str]:
    match = PROPOSITION_RE.fullmatch(proposition)
    if not match:
        raise UnsupportedNormalization("identifiant hors forme PMn:✱x·y")
    return match.group(1), match.group(2)


def _local_statement(block: Block) -> str:
    lines = [line.strip() for line in block.reading.splitlines() if line.strip()]
    if len(lines) != 1:
        detail = "bloc Dem. multiligne" if any(line == "Dem." or line.startswith("Dem.") for line in lines) else "bloc local multiligne"
        raise UnsupportedNormalization(detail)
    _volume, number = _proposition_parts(block.proposition)
    return re.sub(rf"^[✱*]{re.escape(number)}\.\s*", "", lines[0], count=1)


def read_blocks(root: Path) -> list[Block]:
    blocks: list[Block] = []
    seen: dict[str, Block] = {}
    principia = root / "Principia"
    if not principia.is_dir():
        raise ValueError(f"répertoire PM absent: {principia}")
    for path in sorted(principia.rglob("*.lean")):
        text = path.read_text(encoding="utf-8")
        for match in BLOCK_RE.finditer(text):
            begin, reading, end = match.groups()
            line = text.count("\n", 0, match.start()) + 1
            if begin != end:
                raise ValueError(f"bloc PM-VERBATIM désaccordé à {path}:{line}: {begin}/{end}")
            block = Block(begin, reading.strip(), path, line)
            if begin in seen:
                prior = seen[begin]
                raise ValueError(
                    f"bloc PM-VERBATIM dupliqué {begin}: "
                    f"{prior.path}:{prior.line} et {path}:{line}"
                )
            seen[begin] = block
            blocks.append(block)
    if not blocks:
        raise ValueError("aucun bloc PM-VERBATIM trouvé")
    return blocks


def read_witnesses(root: Path, witnesses: dict[str, Path]) -> dict[str, list[str]]:
    readings: dict[str, list[str]] = defaultdict(list)
    for volume, relative in sorted(witnesses.items()):
        path = root / relative
        if not path.is_file():
            raise ValueError(f"témoin absent: {relative}")
        text = path.read_text(encoding="utf-8")
        for match in WITNESS_RE.finditer(text):
            number, reading = match.groups()
            readings[f"{volume}:✱{number}"].append(reading.strip())
    return dict(readings)


def load_exemptions(path: Path) -> dict[str, Exemption]:
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        raise RegistryError(f"registre illisible {path}: {error}") from error
    if not isinstance(payload, dict) or set(payload) != {"schema_version", "exemptions"}:
        raise RegistryError("le registre exige exactement schema_version et exemptions")
    if payload["schema_version"] != 1 or not isinstance(payload["exemptions"], list):
        raise RegistryError("schema_version doit valoir 1 et exemptions doit être une liste")

    required = {"proposition", "gutenberg_reading", "repository_reading", "reason"}
    result: dict[str, Exemption] = {}
    for index, item in enumerate(payload["exemptions"]):
        label = f"exemptions[{index}]"
        if not isinstance(item, dict) or set(item) != required:
            raise RegistryError(f"{label} exige exactement {', '.join(sorted(required))}")
        if any(not isinstance(item[field], str) or not item[field].strip() for field in required):
            raise RegistryError(f"{label} contient un champ vide ou non textuel")
        reason = item["reason"].strip()
        if len(reason) < MIN_REASON_LENGTH:
            raise RegistryError(
                f"{label}.reason doit compter au moins {MIN_REASON_LENGTH} caractères "
                f"(reçu: {len(reason)})"
            )
        proposition = item["proposition"].strip()
        if not PROPOSITION_RE.fullmatch(proposition):
            raise RegistryError(f"{label}.proposition est invalide: {proposition}")
        if proposition in result:
            raise RegistryError(f"exemption dupliquée: {proposition}")
        result[proposition] = Exemption(
            proposition,
            item["gutenberg_reading"].strip(),
            item["repository_reading"].strip(),
            reason,
        )
    return result


def _witness_reading(candidates: list[str]) -> tuple[str, str]:
    normalized: dict[str, list[str]] = defaultdict(list)
    unsupported: list[str] = []
    for reading in candidates:
        try:
            normalized[normalize_reading(reading, tex=True)].append(reading)
        except UnsupportedNormalization as error:
            unsupported.append(str(error))
    if unsupported:
        raise UnsupportedNormalization(
            "au moins une occurrence du témoin est non normalisable: "
            + "; ".join(sorted(set(unsupported)))
        )
    if len(normalized) != 1:
        raise UnsupportedNormalization(
            f"{len(normalized)} leçons Gutenberg normalisées incompatibles"
        )
    canonical, raw_readings = next(iter(normalized.items()))
    return canonical, sorted(set(raw_readings))[0]


def verify(
    root: Path,
    *,
    witnesses: dict[str, Path] | None = None,
    exemptions_path: Path | None = None,
) -> Report:
    witnesses = DEFAULT_WITNESSES if witnesses is None else witnesses
    exemptions_path = DEFAULT_EXEMPTIONS if exemptions_path is None else exemptions_path
    report = Report()
    try:
        exemptions = load_exemptions(root / exemptions_path)
    except RegistryError as error:
        report.registry_errors.append(str(error))
        exemptions = {}

    blocks = read_blocks(root)
    witness_readings = read_witnesses(root, witnesses)
    report.examined = len(blocks)
    used_exemptions: set[str] = set()

    for block in blocks:
        try:
            volume, _number = _proposition_parts(block.proposition)
            if volume not in witnesses:
                raise UnsupportedNormalization(f"aucun témoin configuré pour {volume}")
            candidates = witness_readings.get(block.proposition, [])
            if not candidates:
                raise UnsupportedNormalization("aucune leçon Gutenberg portant cet identifiant")
            local_raw = _local_statement(block)
            local = normalize_reading(local_raw, tex=False)
            gutenberg, gutenberg_raw = _witness_reading(candidates)
        except UnsupportedNormalization as error:
            report.unsupported.append(UnsupportedBlock(block, str(error)))
            continue

        report.compared += 1
        if local == gutenberg:
            report.conforming += 1
            continue

        exemption = exemptions.get(block.proposition)
        if exemption is not None:
            if (
                exemption.gutenberg_reading == gutenberg_raw
                and exemption.repository_reading == local_raw
            ):
                report.exempted += 1
                used_exemptions.add(block.proposition)
                continue
            report.registry_errors.append(
                f"{block.proposition}: exemption périmée; ses deux leçons ne "
                "correspondent pas exactement au témoin et au dépôt actuels"
            )
        report.divergences.append(Divergence(block, gutenberg_raw))

    for proposition in sorted(set(exemptions) - used_exemptions):
        if not any(error.startswith(f"{proposition}:") for error in report.registry_errors):
            report.registry_errors.append(
                f"{proposition}: exemption inutilisée (proposition absente, conforme ou non normalisable)"
            )
    if report.compared == 0:
        report.registry_errors.append(
            "contrôle vide: aucun bloc PM-VERBATIM n'a pu être comparé au témoin"
        )
    return report


def _relative(root: Path, path: Path) -> str:
    try:
        return str(path.relative_to(root))
    except ValueError:
        return str(path)


def _compact_propositions(propositions: list[str]) -> list[str]:
    """Name every proposition in compact, deterministic star-group notation."""
    groups: dict[tuple[str, str], list[str]] = defaultdict(list)
    other: list[str] = []
    for proposition in sorted(propositions):
        match = re.fullmatch(r"(PM\d+):✱(\d+)·(.+)", proposition)
        if match:
            groups[(match.group(1), match.group(2))].append(match.group(3))
        else:
            other.append(proposition)

    compact: list[str] = []
    for (volume, star), suffixes in sorted(groups.items()):
        prefix = f"{volume}:✱{star}·"
        chunk: list[str] = []
        length = len(prefix) + 2
        for suffix in suffixes:
            extra = len(suffix) + (1 if chunk else 0)
            if chunk and length + extra > 105:
                compact.append(prefix + "{" + ",".join(chunk) + "}")
                chunk = []
                length = len(prefix) + 2
            chunk.append(suffix)
            length += extra
        if len(suffixes) == 1:
            compact.append(prefix + suffixes[0])
        elif chunk:
            compact.append(prefix + "{" + ",".join(chunk) + "}")
    compact.extend(other)
    return compact


def _unsupported_category(reason: str) -> str:
    """Keep the unsupported report explicit without one group per command set."""
    if "fraction de substitution TeX" in reason:
        return "fraction de substitution TeX (\\frac)"
    if "environnement TeX" in reason:
        return "environnement TeX array/aligned ou saut de ligne"
    if "indice ou exposant TeX" in reason:
        return "indice ou exposant TeX sans règle diplomatique déclarée"
    if "commande TeX sans règle explicite" in reason:
        return "commande TeX sans règle explicite"
    if "leçons Gutenberg normalisées incompatibles" in reason:
        return "plusieurs leçons Gutenberg normalisées incompatibles"
    return reason


def _append_named(lines: list[str], propositions: list[str], *, indent: str = "  ") -> None:
    for compact in _compact_propositions(propositions):
        wrapped = textwrap.wrap(
            compact,
            width=116,
            initial_indent=indent,
            subsequent_indent=indent + "  ",
            break_long_words=False,
            break_on_hyphens=False,
        )
        lines.extend(wrapped or [indent + compact])


def render_report(report: Report, root: Path, *, report_all: bool = False) -> str:
    lines = [
        "Vérification PM-VERBATIM contre les témoins Gutenberg",
        f"Blocs examinés: {report.examined}",
        f"Blocs comparés: {report.compared}",
        f"Blocs conformes: {report.conforming}",
        f"Blocs exemptés: {report.exempted}",
        f"Blocs divergents: {len(report.divergences)}",
    ]
    if report.divergences:
        lines.append("Divergences (chaque bloc est nommé):")
        _append_named(
            lines,
            [divergence.block.proposition for divergence in report.divergences],
        )
        if report_all:
            lines.append("Détail des divergences:")
            for divergence in report.divergences:
                block = divergence.block
                lines.extend(
                    [
                        f"- {block.proposition} ({_relative(root, block.path)}:{block.line})",
                        f"  Gutenberg: {divergence.gutenberg_reading}",
                        f"  Dépôt: {block.reading}",
                    ]
                )
    else:
        lines.append("Divergences: aucune")

    lines.append(f"Blocs non normalisables: {len(report.unsupported)}")
    if report.unsupported:
        grouped: dict[str, list[str]] = defaultdict(list)
        for unsupported in report.unsupported:
            grouped[_unsupported_category(unsupported.reason)].append(
                unsupported.block.proposition
            )
        lines.append("Non normalisables (chaque bloc est nommé):")
        for reason in sorted(grouped):
            lines.append(f"- {reason} ({len(grouped[reason])}):")
            _append_named(lines, grouped[reason], indent="    ")
    else:
        lines.append("Non normalisables: aucun")

    lines.append(f"Erreurs du registre d'exemptions: {len(report.registry_errors)}")
    for error in report.registry_errors:
        lines.append(f"- {error}")
    status = "ÉCHEC" if report.divergences or report.registry_errors else "SUCCÈS"
    lines.append(f"Résultat du gate: {status}")
    return "\n".join(lines)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT, help=argparse.SUPPRESS)
    parser.add_argument(
        "--report-all",
        action="store_true",
        help="afficher les deux leçons complètes pour chaque divergence",
    )
    arguments = parser.parse_args()
    root = arguments.root.resolve()
    try:
        report = verify(root)
    except (OSError, ValueError) as error:
        print(f"verify_printed_against_witness: erreur: {error}", file=sys.stderr)
        return 2
    print(render_report(report, root, report_all=arguments.report_all))
    return 1 if report.divergences or report.registry_errors else 0


if __name__ == "__main__":
    raise SystemExit(main())
