#!/usr/bin/env python3
"""Deterministic parser foundation for Peano--Russell dot notation.

This first module covers the propositional core and, crucially, models a dot
collection by two directional binding powers.  The same lexer/token protocol
is intended to grow to apparent-variable binders, descriptions, classes and
relations; it is not a regex normalizer for a handful of examples.
"""

from __future__ import annotations

from dataclasses import dataclass
import json
import re
from typing import Iterator


class PMSyntaxError(ValueError):
    pass


@dataclass(frozen=True)
class ScopeMark:
    count: int


@dataclass(frozen=True)
class Token:
    kind: str
    text: str
    position: int
    left_scope: int = 0
    right_scope: int = 0


@dataclass(frozen=True)
class AST:
    tag: str
    children: tuple["AST", ...] = ()
    value: str | None = None

    def to_dict(self) -> dict:
        result = {"tag": self.tag}
        if self.value is not None:
            result["value"] = self.value
        if self.children:
            result["children"] = [child.to_dict() for child in self.children]
        return result


OPERATORS = {
    "∨": "or", "⊃": "implies", "≡": "equiv", "=": "equal", "≠": "not_equal", "∈": "member",
    "∩": "class_intersection", "∪": "class_union", "⊂": "class_inclusion",
    "∩̇": "relation_intersection", "⋃̇": "relation_union",
    "⊂̇": "relation_inclusion", "|": "relative_product",
    "→": "function_relation",
    "sm": "similar",
    "∼∈": "not_member",
}
GREEK_FUNCTION_SYMBOLS = "φψχθ"
CLASS_SYMBOLS = "αβγκ"
RELATION_SYMBOLS = "RSPQJ"
OF = "ʻ"


def mark_count(text: str) -> int:
    """A colon is typographically two dots; mixed groups add normally."""
    return text.count(".") + text.count("·") + 2 * text.count(":")


def raw_tokens(source: str) -> list[Token]:
    result: list[Token] = []
    index = 0
    while index < len(source):
        char = source[index]
        if char.isspace():
            index += 1
            continue
        if source.startswith("⊢", index):
            result.append(Token("assert", "⊢", index))
            index += 1
            continue
        if source.startswith("x̂ŷ", index):
            result.append(Token("relation_binder", "x̂ŷ", index))
            index += len("x̂ŷ")
            continue
        # PM also uses a single relation variable with a circumflex as an
        # abstraction binder, e.g. `P̂(condition)` in ✱250·01.  This is not
        # the class abstraction `α̂(condition)`: retain the printed bound
        # relation symbol so its eventual contextual owner can distinguish
        # the two incomplete symbols.
        relation_abstraction = re.match(r"([RSPQJ])̂(?=\s*[\({])", source[index:])
        if relation_abstraction:
            text = relation_abstraction.group(0)
            result.append(Token("relation_binder", text, index))
            index += len(text)
            continue
        if source.startswith("E!", index):
            result.append(Token("existence_predicate", "E!", index))
            index += len("E!")
            continue
        if source.startswith("∃!", index):
            result.append(Token("unique_existence_predicate", "∃!", index))
            index += len("∃!")
            continue
        if source.startswith("∼∈", index):
            result.append(Token("operator", "∼∈", index))
            index += len("∼∈")
            continue
        # The turned comma is PM's postfix/infix ``of`` operator: `Rʻx`
        # denotes the selected value of a relation/function at its argument.
        # It is distinct from both the converse caron and an identifier mark.
        if char == OF:
            end = index + 1
            while end < len(source) and source[end] == OF:
                end += 1
            result.append(Token("of", source[index:end], index))
            index = end
            continue
        # U+1D5F `ᵟ` records the raised type-index printed as ξ in the
        # facsimile.  It is a diplomatic transcription marker, not a claim
        # that Unicode supplies a distinct subscript xi character.
        similar = re.match(r"sm(?:ᵟ|₍[₀-₉ₐ-ₜᵢⱼₓᵧᵩφψχθᵝᵦ,]+₎)?", source[index:])
        if (similar and similar.group(0) != "sm" and
                index + len(similar.group(0)) < len(source) and
                source[index + len(similar.group(0))] == OF):
            text = similar.group(0)
            result.append(Token("type_index", text, index))
            index += len(text)
            continue
        if similar and (
                index + len(similar.group(0)) == len(source) or
                source[index + len(similar.group(0))].isspace()):
            text = similar.group(0)
            result.append(Token("operator", text, index))
            index += len(text)
            continue
        decorated_relation_operator = next(
            (operator for operator in ("∩̇", "⋃̇", "⊂̇")
             if source.startswith(operator, index)),
            None,
        )
        if decorated_relation_operator:
            result.append(Token("operator", decorated_relation_operator, index))
            index += len(decorated_relation_operator)
            continue
        relation_converse = re.match(r"([RSPQ])̌(?![A-Za-z])", source[index:])
        if relation_converse:
            text = relation_converse.group(0)
            result.append(Token("relation_converse", text, index))
            index += len(text)
            continue
        relation_power = re.match(r"([RSPQ])²(?![A-Za-z])", source[index:])
        if relation_power:
            text = relation_power.group(0)
            result.append(Token("relation_power", text, index))
            index += len(text)
            continue
        if char == "ẑ":
            result.append(Token("class_binder", char, index))
            index += 1
            continue
        # `Cl ex` is a printed two-word class operator.  Keeping it as one
        # lexical atom prevents the space from being mistaken for an omitted
        # logical product in the ✱250 definition.
        if source.startswith("Cl ex", index):
            result.append(Token("atom", "Cl ex", index))
            index += len("Cl ex")
            continue
        type_index = re.match(
            r"([A-Za-zΑ-Ωα-ω][A-Za-z0-9_Α-Ωα-ω′'\u0300-\u036f]*)"
            r"(ᵗʻ[Α-Ωα-ω]|ᵅ|ᵝ|ᵦ|ᵟ|ₐ|ₚₒ|ₚ|ₓ|₍[₀-₉ₐ-ₜᵢⱼₓᵧᵩφψχθ,]+₎)",
            source[index:],
        )
        if type_index:
            text = type_index.group(0)
            result.append(Token("type_index", text, index))
            index += len(text)
            continue
        class_binder = re.match(r"([Α-Ωα-ω])̂(?=\s*[\({])", source[index:])
        if class_binder:
            text = class_binder.group(0)
            result.append(Token("class_binder", text, index))
            index += len(text)
            continue
        if char in CLASS_SYMBOLS:
            result.append(Token("class_symbol", char, index))
            index += 1
            continue
        if char == "(":
            description = re.match(
                r"\(\s*℩\s*([A-Za-zΑ-Ωα-ω][A-Za-z0-9_Α-Ωα-ω′']*)\s*\)",
                source[index:],
            )
            if description:
                text = description.group(0)
                result.append(Token("description_binder", text, index))
                index += len(text)
                continue
            binder = (None if result and result[-1].kind in {
                "description_binder", "atom", "type_index", "rparen"
            } else re.match(
                r"\(\s*(∃)?\s*([A-Za-zΑ-Ωα-ω][A-Za-z0-9_Α-Ωα-ω′']*"
                r"(?:\s*,\s*[A-Za-zΑ-Ωα-ω][A-Za-z0-9_Α-Ωα-ω′']*)*)\s*\)"
                r"(?=\s*[\.:])",
                source[index:],
            ))
            if binder:
                text = binder.group(0)
                kind = "exists_binder" if binder.group(1) else "forall_binder"
                result.append(Token(kind, text, index))
                index += len(text)
                continue
        if char in ".:·":
            end = index + 1
            while end < len(source) and source[end] in ".:·":
                end += 1
            text = source[index:end]
            result.append(Token("mark", text, index, mark_count(text), mark_count(text)))
            index = end
            continue
        if char in {"≡", "⊃"}:
            decorated = re.match(
                rf"{re.escape(char)}(?:[₀-₉ₐ-ₜᵢⱼₓᵧᵩφψχθ]+(?:,[₀-₉ₐ-ₜᵢⱼₓᵧᵩφψχθ]+)*)?",
                source[index:],
            )
            text = decorated.group(0) if decorated else char
            result.append(Token("operator", text, index))
            index += len(text)
            continue
        if char in OPERATORS:
            result.append(Token("operator", char, index))
            index += 1
            continue
        if char in "∼¬~":
            result.append(Token("neg", char, index))
            index += 1
            continue
        if char == "−":
            if source.startswith("−̇", index):
                result.append(Token("relation_neg", "−̇", index))
                index += len("−̇")
            elif result and result[-1].kind in {
                    "atom", "class_symbol", "rparen", "relation_symbol"}:
                result.append(Token("operator", char, index))
                index += 1
            else:
                result.append(Token("class_neg", char, index))
                index += 1
            continue
        if char in "([{":
            result.append(Token("lparen", char, index))
            index += 1
            continue
        type_marked_value = re.match(r"(?:[A-Za-z]↓|↓[A-Za-z])(?=ʻ)", source[index:])
        if type_marked_value:
            text = type_marked_value.group(0)
            result.append(Token("atom", text, index))
            index += len(text)
            continue
        relation_value = re.match(r"([a-z])([RSPQ])([a-z])", source[index:])
        if relation_value:
            text = relation_value.group(0)
            result.append(Token("relation_value", text, index))
            index += len(text)
            continue
        if char in RELATION_SYMBOLS and (index + 1 == len(source) or not source[index + 1].isalpha()):
            result.append(Token("relation_symbol", char, index))
            index += 1
            continue
        if char in ")]}" :
            result.append(Token("rparen", char, index))
            index += 1
            continue
        if char == ",":
            result.append(Token("comma", char, index))
            index += 1
            continue
        if char in GREEK_FUNCTION_SYMBOLS or (
            char in "fg" and index + 1 < len(source) and source[index + 1] in "!({"
        ):
            result.append(Token("function", char, index))
            index += 1
            continue
        # Bare `∃` is a printed class operator in the ✱250·01 matrix; it is
        # distinct from the already-tokenised `∃!` existence predicate.
        if char == "∃":
            result.append(Token("atom", char, index))
            index += 1
            continue
        if char == "!":
            result.append(Token("bang", char, index))
            index += 1
            continue
        if char == "ₐ":
            result.append(Token("postfix_type_index", char, index))
            index += 1
            continue
        superscript_indexed = re.match(
            r"([A-Za-zΑ-Ωα-ω]+)([⁰¹²³⁴-⁹]|⁽[⁰¹²³⁴-⁹]+⁾)([A-Za-zΑ-Ωα-ω]*)",
            source[index:],
        )
        if superscript_indexed:
            text = superscript_indexed.group(0)
            result.append(Token("superscript_indexed", text, index))
            index += len(text)
            continue
        if char.isascii() and char.isdigit():
            match = re.match(r"[0-9]+", source[index:])
            assert match is not None
            text = match.group(0)
            result.append(Token("atom", text, index))
            index += len(text)
            continue
        match = re.match(
            r"[A-Za-zΑ-Ωα-ωᗡ][A-Za-z0-9_Α-Ωα-ωᗡ₀-₉′'\u0300-\u036f]*",
            source[index:],
        )
        if match:
            text = match.group(0)
            result.append(Token("atom", text, index))
            index += len(text)
            continue
        raise PMSyntaxError(f"unexpected character {char!r} at offset {index}")
    return result


def attach_scope_marks(tokens: list[Token]) -> list[Token]:
    """Attach Group-I marks to adjacent connectives; leave Group III products.

    A mark immediately next to ∨/⊃/≡ brackets that connective. Every remaining
    mark is a logical product. This is the primary lexical distinction stated
    by PM on printed pp. 9--10.
    """
    consumed: set[int] = set()
    result: list[Token] = []
    # Group II: a mark following an apparent-variable bracket works forward.
    for index, token in enumerate(tokens):
        if token.kind not in {"forall_binder", "exists_binder"}:
            continue
        following = (tokens[index + 1]
                     if index + 1 < len(tokens) and tokens[index + 1].kind == "mark" else None)
        if following is not None:
            consumed.add(index + 1)
            tokens[index] = Token(
                token.kind, token.text, token.position,
                right_scope=following.right_scope,
            )
    for index, token in enumerate(tokens):
        if token.kind != "operator":
            continue
        left = tokens[index - 1] if index and tokens[index - 1].kind == "mark" else None
        right = (tokens[index + 1]
                 if index + 1 < len(tokens) and tokens[index + 1].kind == "mark" else None)
        if left is not None:
            consumed.add(index - 1)
        if right is not None:
            consumed.add(index + 1)
        tokens[index] = Token(
            "binary", token.text, token.position,
            left.left_scope if left else 0,
            right.right_scope if right else 0,
        )
    for index, token in enumerate(tokens):
        if index in consumed:
            continue
        if token.kind == "operator":
            # The list was mutated above, so this branch is defensive only.
            token = Token("binary", token.text, token.position)
        elif token.kind == "mark":
            token = Token("binary", "·", token.position,
                          token.left_scope, token.right_scope)
        result.append(token)
    return result


def binding_power(token: Token, side: str) -> int:
    scope = token.left_scope if side == "left" else token.right_scope
    if scope:
        # More dots mean a more external bracket. At equal count, Group I
        # (a marked connective) is external to Group III (logical product).
        group_force = 10 if token.text != "·" else 0
        return 1000 - 100 * scope - group_force
    if token.text.startswith("≡") or (token.text.startswith("⊃") and token.text != "⊃"):
        return 1100
    if token.text.startswith("sm"):
        return 1450
    return {
        "⊃": 1200, "∨": 1300, "·": 1400, "=": 1450, "≠": 1450, "∈": 1450,
        "∼∈": 1450,
        "⊂": 1450, "∪": 1500, "∩": 1510, "−": 1500,
        "⊂̇": 1450, "⋃̇": 1500, "∩̇": 1510, "|": 1520, "→": 1520,
        "sm": 1450,
    }[token.text]


def binder_binding_power(token: Token) -> int:
    if token.right_scope:
        # Group II lies strictly between Group I and Group III at equal count.
        return 1000 - 100 * token.right_scope - 5
    return 1000


def binder_variables(text: str) -> str:
    interior = text[text.index("(") + 1:text.rindex(")")]
    interior = interior.replace("∃", "", 1)
    return ",".join(part.strip() for part in interior.split(","))


def description_variable(text: str) -> str:
    interior = text[text.index("(") + 1:text.rindex(")")]
    return interior.replace("℩", "", 1).strip()


def operator_tag(text: str) -> tuple[str, str | None]:
    if text == "−":
        return "class_difference", None
    if text.startswith("≡") and text != "≡":
        return "formal_equiv", text[1:]
    if text.startswith("⊃") and text != "⊃":
        return "formal_implies", text[1:]
    if text.startswith("sm"):
        return "similar", text[2:] or None
    return OPERATORS.get(text, "and"), None


def bind_description_occurrences(node: AST, variable: str, condition: AST) -> AST:
    """Eliminate matching surface descriptions inside their explicit scope.

    The returned object AST has no description-valued term: occurrences of the
    printed incomplete symbol become a bound placeholder owned by the
    surrounding `description_scope` node.
    """
    if node.tag == "description" and node.value == variable and node.children == (condition,):
        return AST("description_bound", value=variable)
    return AST(
        node.tag,
        tuple(bind_description_occurrences(child, variable, condition)
              for child in node.children),
        node.value,
    )


def surface_descriptions(node: AST) -> list[AST]:
    """Return distinct unscoped descriptions in deterministic print order."""
    found: list[AST] = []
    if node.tag == "description" and node not in found:
        found.append(node)
    for child in node.children:
        for entry in surface_descriptions(child):
            if entry not in found:
                found.append(entry)
    return found


def contains_incomplete_symbol(node: AST) -> bool:
    return node.tag in {
        "description", "class_incomplete", "class_symbol", "class_union",
        "class_intersection", "class_complement", "relation_incomplete",
        "relation_symbol", "relation_union", "relation_intersection",
        "relation_complement", "relative_product", "relation_converse",
        "relation_power",
    } or any(
        contains_incomplete_symbol(child) for child in node.children
    )


def relation_binder_variables(text: str) -> str:
    if text == "x̂ŷ":
        return "x,y"
    if text.endswith("̂"):
        return text[:-1]
    return text


def is_class_surface(node: AST) -> bool:
    return node.tag in {
        "class_incomplete", "class_symbol", "class_union",
        "class_intersection", "class_difference", "class_complement", "of",
    }


def seal_class_surface(node: AST) -> AST:
    """Move a surface class expression beneath a contextual owner."""
    mapping = {
        "class_incomplete": "class_comprehension_spec",
        "class_symbol": "class_reference",
        "class_union": "class_union_spec",
        "class_intersection": "class_intersection_spec",
        "class_difference": "class_difference_spec",
        "class_complement": "class_complement_spec",
        # A value stroke is type-sensitive in PM.  In a class-only context it
        # is sealed as a class-valued application without guessing its type
        # outside that context.
        "of": "class_of_value",
    }
    if node.tag not in mapping:
        raise PMSyntaxError(f"not a class surface expression: {node.tag}")
    return AST(
        mapping[node.tag],
        tuple(seal_class_surface(child) if is_class_surface(child) else child
              for child in node.children),
        node.value,
    )


def is_class_context_candidate(node: AST) -> bool:
    """Whether PM's surrounding class syntax supplies a class reading."""
    return (
        is_class_surface(node) or node.tag == "atom" or
        (node.tag == "type_indexed" and node.children[0].tag == "atom") or
        (node.tag == "apply_named" and is_class_context_candidate(node.children[0]))
    )


def seal_as_class(node: AST) -> AST:
    """Seal a surface class, or a printed class constant, in class context."""
    if is_class_surface(node):
        return seal_class_surface(node)
    if node.tag == "atom":
        return AST("class_constant_reference", value=node.value)
    if node.tag == "type_indexed" and node.children[0].tag == "atom":
        return AST(
            "class_type_indexed",
            (seal_as_class(node.children[0]),),
            node.value,
        )
    if node.tag == "apply_named" and is_class_context_candidate(node.children[0]):
        return AST(
            "class_named_application",
            (seal_as_class(node.children[0]), *node.children[1:]),
        )
    raise PMSyntaxError(f"not a class expression in this context: {node.tag}")


def is_relation_surface(node: AST) -> bool:
    return node.tag in {
        "relation_incomplete", "relation_symbol", "relation_union",
        "relation_intersection", "relation_complement", "relative_product",
        "relation_converse", "relation_power", "function_relation",
    } or (node.tag == "type_indexed" and is_relation_surface(node.children[0]))


def seal_relation_surface(node: AST) -> AST:
    mapping = {
        "relation_incomplete": "relation_comprehension_spec",
        "relation_symbol": "relation_reference",
        "relation_union": "relation_union_spec",
        "relation_intersection": "relation_intersection_spec",
        "relation_complement": "relation_complement_spec",
        "relative_product": "relative_product_spec",
        "relation_converse": "relation_converse_spec",
        "relation_power": "relation_power_spec",
        "function_relation": "function_relation_spec",
        "type_indexed": "relation_type_indexed",
    }
    if node.tag not in mapping:
        raise PMSyntaxError(f"not a relation surface expression: {node.tag}")
    return AST(
        mapping[node.tag],
        tuple(seal_relation_surface(child) if is_relation_surface(child) else child
              for child in node.children),
        node.value,
    )


class Parser:
    def __init__(self, source: str):
        self.tokens = attach_scope_marks(raw_tokens(source))
        self.index = 0

    def peek(self) -> Token | None:
        return self.tokens[self.index] if self.index < len(self.tokens) else None

    def take(self) -> Token:
        token = self.peek()
        if token is None:
            raise PMSyntaxError("unexpected end of formula")
        self.index += 1
        return token

    def parse(self) -> AST:
        asserted = self.peek() is not None and self.peek().kind == "assert"
        if asserted:
            self.take()
            # Dots following ⊢ are assertion scope, not object syntax.
            while self.peek() is not None and self.peek().kind == "binary" and self.peek().text == "·":
                self.take()
        expression = self.expression(0)
        if self.peek() is not None:
            token = self.peek()
            raise PMSyntaxError(f"unconsumed token {token.text!r} at offset {token.position}")
        result = AST("assert", (expression,)) if asserted else expression
        if contains_incomplete_symbol(result):
            raise PMSyntaxError("an incomplete symbol occurs without an explicit context of use")
        return result

    def expression(self, minimum: int) -> AST:
        token = self.take()
        if token.kind == "atom":
            left = AST("atom", value=token.text)
        elif token.kind == "superscript_indexed":
            indexed = re.fullmatch(
                r"(?P<head>[A-Za-zΑ-Ωα-ω]+)(?P<index>[⁰¹²³⁴-⁹]|⁽[⁰¹²³⁴-⁹]+⁾)(?P<tail>[A-Za-zΑ-Ωα-ω]*)",
                token.text,
            )
            assert indexed is not None
            left = AST(
                "superscript_indexed",
                (AST("atom", value=indexed.group("head") + indexed.group("tail")),),
                indexed.group("index"),
            )
        elif token.kind == "type_index":
            indexed = re.fullmatch(
                r"(?P<head>[A-Za-zΑ-Ωα-ω][A-Za-z0-9_Α-Ωα-ω′'\u0300-\u036f]*)"
                r"(?P<index>ᵗʻ[Α-Ωα-ω]|ᵅ|ᵝ|ᵦ|ᵟ|ₐ|ₚₒ|ₚ|ₓ|₍[₀-₉ₐ-ₜᵢⱼₓᵧᵩφψχθ,]+₎)",
                token.text,
            )
            assert indexed is not None
            head = indexed.group("head")
            left = AST(
                "type_indexed",
                (AST("relation_symbol" if head in RELATION_SYMBOLS else "atom", value=head),),
                indexed.group("index"),
            )
        elif token.kind == "function":
            left = self.application(token)
        elif token.kind == "existence_predicate":
            value = self.expression(1700)
            if value.tag == "of":
                left = AST("exists_value", (value,))
            elif value.tag == "description":
                left = AST("description_exists", value.children, value.value)
            else:
                raise PMSyntaxError("E! requires a PM `of` application or description")
        elif token.kind == "unique_existence_predicate":
            value = self.expression(1500)
            left = AST(
                "exists_unique",
                (seal_class_surface(value) if is_class_surface(value) else value,),
            )
        elif token.kind == "description_binder":
            condition = self.parenthesized_argument()
            left = AST("description", (condition,), description_variable(token.text))
        elif token.kind == "of":
            # A leading value stroke is PM's unit-class notation.  Multiple
            # strokes retain their printed nesting rather than being folded
            # into a generic application node.
            value = self.expression(1701)
            if is_class_surface(value):
                value = seal_class_surface(value)
            elif is_relation_surface(value):
                value = seal_relation_surface(value)
            left = value
            for _ in token.text:
                left = AST("unit_class", (left,))
        elif token.kind == "class_binder":
            condition = (
                self.parenthesized_argument()
                if token.text == "ẑ" or self.peek().text == "("
                else self.braced_argument()
            )
            left = AST("class_incomplete", (condition,), token.text[0])
        elif token.kind == "class_symbol":
            left = AST("class_symbol", value=token.text)
        elif token.kind == "class_neg":
            operand = self.expression(1600)
            if not is_class_surface(operand):
                raise PMSyntaxError("class complement requires a class expression")
            left = AST("class_complement", (operand,))
        elif token.kind == "relation_binder":
            condition = self.expression(1500)
            left = AST(
                "relation_incomplete", (condition,), relation_binder_variables(token.text)
            )
        elif token.kind == "relation_symbol":
            left = AST("relation_symbol", value=token.text)
        elif token.kind == "relation_converse":
            left = AST("relation_converse", (AST("relation_symbol", value=token.text[0]),))
        elif token.kind == "relation_power":
            left = AST("relation_power", (AST("relation_symbol", value=token.text[0]),), "2")
        elif token.kind == "relation_neg":
            operand = self.expression(1600)
            if not is_relation_surface(operand):
                raise PMSyntaxError("relation complement requires a relation expression")
            left = AST("relation_complement", (operand,))
        elif token.kind == "relation_value":
            left = AST(
                "relation_value",
                (AST("atom", value=token.text[0]), AST("atom", value=token.text[2])),
                token.text[1],
            )
        elif token.kind == "neg":
            left = AST("not", (self.expression(1500),))
        elif token.kind in {"forall_binder", "exists_binder"}:
            body = self.expression(binder_binding_power(token))
            left = AST(
                "forall" if token.kind == "forall_binder" else "exists",
                (body,),
                binder_variables(token.text),
            )
        elif token.kind == "lparen":
            left = self.expression(0)
            bracketed_descriptions = [left]
            if token.text == "[":
                while self.peek() is not None and self.peek().kind == "comma":
                    self.take()
                    bracketed_descriptions.append(self.expression(0))
            close = self.take()
            if close.kind != "rparen":
                raise PMSyntaxError(f"missing closing bracket before offset {close.position}")
            if token.text == "[":
                if not all(entry.tag == "description" for entry in bracketed_descriptions):
                    raise PMSyntaxError("description brackets require description entries")
                marker = self.peek()
                if marker is None or marker.kind != "binary" or marker.text != "·":
                    raise PMSyntaxError("a bracketed description must be followed by a scope mark")
                marker = self.take()
                continuation = self.expression(binding_power(marker, "right"))
                for entry in bracketed_descriptions:
                    continuation = bind_description_occurrences(
                        continuation, entry.value or "", entry.children[0]
                    )
                # Descriptions not named by the outer bracket retain their
                # narrow, in-place scope.  Materialise that scope explicitly
                # before wrapping the bracketed (outer) descriptions.
                implicit_descriptions = surface_descriptions(continuation)
                for entry in implicit_descriptions:
                    continuation = bind_description_occurrences(
                        continuation, entry.value or "", entry.children[0]
                    )
                for entry in reversed(implicit_descriptions):
                    continuation = AST(
                        "description_scope", (entry.children[0], continuation), entry.value
                    )
                left = continuation
                for entry in reversed(bracketed_descriptions):
                    left = AST(
                        "description_scope", (entry.children[0], left), entry.value
                    )
        else:
            raise PMSyntaxError(f"expected proposition at offset {token.position}")

        while (next_token := self.peek()) is not None:
            if next_token.kind == "comma" and minimum == 0:
                # A top-level comma-list before membership is a tuple of
                # terms, not the separator consumed by named applications.
                lookahead = self.tokens[self.index + 1:]
                if not any(token.kind == "binary" and token.text == "∈"
                           for token in lookahead):
                    break
                self.take()
                right = self.expression(1600)
                left = AST(
                    "tuple",
                    (*left.children, right) if left.tag == "tuple" else (left, right),
                )
                continue
            if next_token.kind == "postfix_type_index":
                if 1800 < minimum:
                    break
                index = self.take()
                left = AST("type_indexed", (left,), index.text)
                continue
            if next_token.kind == "superscript_indexed":
                if 1800 < minimum:
                    break
                index = self.take()
                left = AST("superscript_indexed", (left,), index.text)
                continue
            if (next_token.kind == "lparen" and next_token.text == "(" and
                    left.tag in {"atom", "type_indexed", "apply_named"}):
                if 1800 < minimum:
                    break
                arguments = tuple(
                    seal_as_class(argument) if is_class_surface(argument) else argument
                    for argument in self.parenthesized_arguments()
                )
                left = AST("apply_named", (left, *arguments))
                continue
            if next_token.kind == "of":
                # PM's turned comma binds more tightly than every dot group.
                # Equal `of` strokes associate to the left, preserving the
                # printed nesting in terms such as `sʻClʻʻ2`.
                if 1700 < minimum:
                    break
                operator = self.take()
                right = self.expression(1701)
                if is_class_surface(right):
                    right = seal_class_surface(right)
                elif is_relation_surface(right):
                    right = seal_relation_surface(right)
                left = AST(
                    "of", (left, right),
                    operator.text if len(operator.text) > 1 else None,
                )
                continue
            if next_token.kind != "binary":
                break
            left_bp = binding_power(next_token, "left")
            if left_bp < minimum:
                break
            operator = self.take()
            right_minimum = binding_power(operator, "right")
            # PM records the n-ary surface conventions as left-associated
            # (✱2·33 for disjunction, ✱3·02/✱4·34 for products). This also
            # governs a tie between successive symmetrically Group-I-marked
            # connectives, e.g. `p . ∨ . q . ∨ . r`: equal scope marks do
            # not silently reverse the convention. Implication remains
            # right-associated, and unequal directional scope marks continue
            # to determine their own bracketing.
            tied_marked_product_or_sum = (
                operator.left_scope != 0 and
                operator.left_scope == operator.right_scope
            )
            if (operator.text in {"∨", "·"} and
                    (operator.right_scope == 0 or tied_marked_product_or_sum)):
                right_minimum += 1
            right = self.expression(right_minimum)
            tag, value = operator_tag(operator.text)
            if tag in {"class_union", "class_intersection"}:
                if not is_class_context_candidate(left) or not is_class_context_candidate(right):
                    raise PMSyntaxError(f"{operator.text} requires two class expressions")
                left = AST(tag, (seal_as_class(left), seal_as_class(right)))
            elif tag == "class_difference":
                left = AST(
                    "class_difference",
                    (seal_as_class(left) if is_class_context_candidate(left) else left,
                     seal_as_class(right) if is_class_context_candidate(right) else right),
                )
            elif tag == "not_equal":
                left = AST(
                    "not_equal",
                    (seal_as_class(left) if is_class_context_candidate(left) else left,
                     seal_as_class(right) if is_class_context_candidate(right) else right),
                )
            elif tag in {"relation_union", "relation_intersection", "relative_product"}:
                if not is_relation_surface(left) or not is_relation_surface(right):
                    raise PMSyntaxError(f"{operator.text} requires two relation expressions")
                left = AST(tag, (left, right))
            elif tag == "function_relation":
                left = AST(tag, (left, right))
            elif tag == "member" and is_relation_surface(left):
                left = AST(
                    "relation_membership",
                    (
                        seal_relation_surface(left),
                        seal_relation_surface(right)
                        if is_relation_surface(right) else right,
                    ),
                )
            elif tag == "not_member":
                left = AST("not_member", (left, right))
            elif tag == "member" and is_class_context_candidate(right):
                left = AST(
                    "class_membership",
                    (seal_as_class(left) if is_class_context_candidate(left) else left,
                     seal_as_class(right)),
                )
            elif tag == "member" and is_class_surface(left):
                left = AST("member", (seal_class_surface(left), right))
            elif tag == "similar":
                left = AST(
                    "similar",
                    (seal_class_surface(left) if is_class_surface(left) else left,
                     seal_class_surface(right) if is_class_surface(right) else right),
                    value,
                )
            elif tag == "class_inclusion":
                # In the volume-III facsimile, the inclusion glyph in
                # `Pₚₒ ⊂ J` carries no separate relation dot.  Its operands
                # nonetheless determine a relation inclusion; do not coerce
                # either relation into a class to accommodate typography.
                if is_relation_surface(left) and is_relation_surface(right):
                    left = AST(
                        "relation_inclusion",
                        (seal_relation_surface(left), seal_relation_surface(right)),
                    )
                    continue
                if (not is_class_context_candidate(left) or
                        not is_class_context_candidate(right)):
                    raise PMSyntaxError("class inclusion requires two class expressions")
                left = AST(
                    "class_inclusion", (seal_as_class(left), seal_as_class(right))
                )
            elif tag == "relation_inclusion":
                if not is_relation_surface(left) or not is_relation_surface(right):
                    raise PMSyntaxError("relation inclusion requires two relation expressions")
                left = AST(
                    "relation_inclusion",
                    (seal_relation_surface(left), seal_relation_surface(right)),
                )
            elif tag == "equal" and is_class_surface(left) and is_class_surface(right):
                left = AST(
                    "class_extensional_equal",
                    (seal_class_surface(left), seal_class_surface(right)),
                )
            elif tag == "equal" and is_class_surface(right):
                left = AST("class_defined_equal", (left, seal_class_surface(right)))
            elif tag == "equal" and is_class_surface(left):
                left = AST("class_defined_equal", (right, seal_class_surface(left)))
            elif tag == "equal" and is_relation_surface(left) and is_relation_surface(right):
                left = AST(
                    "relation_extensional_equal",
                    (seal_relation_surface(left), seal_relation_surface(right)),
                )
            elif tag == "equal" and is_relation_surface(right):
                left = AST("relation_defined_equal", (left, seal_relation_surface(right)))
            elif tag == "equal" and is_relation_surface(left):
                left = AST("relation_defined_equal", (right, seal_relation_surface(left)))
            else:
                left = AST(tag, (left, right), value)
        return left

    def parenthesized_argument(self) -> AST:
        opening = self.take()
        if opening.kind != "lparen" or opening.text != "(":
            raise PMSyntaxError(f"expected parenthesized matrix at offset {opening.position}")
        argument = self.expression(0)
        closing = self.take()
        if closing.kind != "rparen" or closing.text != ")":
            raise PMSyntaxError(f"missing closing matrix bracket before offset {closing.position}")
        return argument

    def parenthesized_arguments(self) -> list[AST]:
        opening = self.take()
        if opening.kind != "lparen" or opening.text != "(":
            raise PMSyntaxError(f"expected parenthesized arguments at offset {opening.position}")
        arguments: list[AST] = []
        while True:
            arguments.append(self.expression(0))
            separator = self.take()
            if separator.kind == "rparen" and separator.text == ")":
                return arguments
            if separator.kind != "comma":
                raise PMSyntaxError(f"expected comma at offset {separator.position}")

    def braced_argument(self) -> AST:
        opening = self.take()
        if opening.kind != "lparen" or opening.text != "{":
            raise PMSyntaxError(f"expected braced matrix at offset {opening.position}")
        argument = self.expression(0)
        closing = self.take()
        if closing.kind != "rparen" or closing.text != "}":
            raise PMSyntaxError(f"missing closing matrix brace before offset {closing.position}")
        return argument

    def application(self, function: Token) -> AST:
        predicative = self.peek() is not None and self.peek().kind == "bang"
        if predicative:
            self.take()
        arguments: list[AST] = []
        next_token = self.peek()
        if next_token is not None and next_token.kind == "lparen" and next_token.text in "({":
            opening = self.take()
            expected_close = ")" if opening.text == "(" else "}"
            while True:
                arguments.append(self.expression(0))
                separator = self.take()
                if separator.kind == "rparen" and separator.text == expected_close:
                    break
                if separator.kind != "comma":
                    raise PMSyntaxError(f"expected comma at offset {separator.position}")
        elif next_token is not None and next_token.kind in {"atom", "description_binder"}:
            argument_token = self.take()
            if argument_token.kind == "atom":
                arguments.append(AST("atom", value=argument_token.text))
            else:
                condition = self.parenthesized_argument()
                arguments.append(AST(
                    "description", (condition,), description_variable(argument_token.text)
                ))
        else:
            raise PMSyntaxError(f"function {function.text!r} has no argument")
        application_tag = "apply_predicative" if predicative else "apply_general"
        if len(arguments) == 1 and is_class_surface(arguments[0]):
            incomplete = arguments[0]
            continuation = AST(
                application_tag, (AST("class_bound"),), function.text
            )
            return AST("class_scope", (seal_class_surface(incomplete), continuation))
        if len(arguments) == 1 and is_relation_surface(arguments[0]):
            incomplete = arguments[0]
            continuation = AST(
                application_tag, (AST("relation_bound"),), function.text
            )
            return AST(
                "relation_scope", (seal_relation_surface(incomplete), continuation)
            )
        return AST(application_tag, tuple(arguments), function.text)


def parse(source: str) -> AST:
    return Parser(source).parse()


ITEM_PREFIX = re.compile(r"^\s*✱[0-9]+·[0-9]+\.\s*")
DEFINITION_SIGN = re.compile(r"\s*([.:]+)\s*=\s*([.:]+)\s*")


def parse_statement(source: str) -> AST:
    """Parse a complete numbered formula or definition line.

    Numbering and the terminal `Df` are editorial attributes; the definition
    sign itself becomes an object in the parsed record rather than an equality
    proposition.
    """
    body = ITEM_PREFIX.sub("", source, count=1).strip()
    body = re.sub(r"\s+\[[^\]]+\]\s*$", "", body).strip()
    body = re.sub(r"\s+(?:Df|Pp)\.?\s*$", "", body).strip()
    match = DEFINITION_SIGN.search(body)
    if match:
        left_text = body[:match.start()].strip()
        right_text = body[match.end():].strip()
        if not left_text or not right_text:
            raise PMSyntaxError("definition sign has an empty side")
        return AST("definition", (parse(left_text), parse(right_text)))
    return parse(body)


def main(arguments: list[str] | None = None) -> None:
    import argparse
    cli = argparse.ArgumentParser()
    cli.add_argument("formula")
    options = cli.parse_args(arguments)
    print(json.dumps(parse_statement(options.formula).to_dict(), ensure_ascii=False, sort_keys=True))


if __name__ == "__main__":
    main()
