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


OPERATORS = {"∨": "or", "⊃": "implies", "≡": "equiv", "=": "equal", "∈": "member"}
GREEK_FUNCTION_SYMBOLS = "φψχθ"


def mark_count(text: str) -> int:
    """A colon is typographically two dots; mixed groups add normally."""
    return text.count(".") + 2 * text.count(":")


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
        if char == "ẑ":
            result.append(Token("class_binder", char, index))
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
            binder = (None if result and result[-1].kind == "description_binder" else re.match(
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
        if char in ".:":
            end = index + 1
            while end < len(source) and source[end] in ".:":
                end += 1
            text = source[index:end]
            result.append(Token("mark", text, index, mark_count(text), mark_count(text)))
            index = end
            continue
        if char == "≡":
            decorated = re.match(
                r"≡(?:[₀-₉ₐ-ₜᵢⱼₓᵧᵩφψχθ]+(?:,[₀-₉ₐ-ₜᵢⱼₓᵧᵩφψχθ]+)*)?",
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
        if char in "([{":
            result.append(Token("lparen", char, index))
            index += 1
            continue
        relation_value = re.match(r"([a-z])([RSPQ])([a-z])", source[index:])
        if relation_value:
            text = relation_value.group(0)
            result.append(Token("relation_value", text, index))
            index += len(text)
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
        if char == "!":
            result.append(Token("bang", char, index))
            index += 1
            continue
        match = re.match(
            r"[A-Za-zΑ-Ωα-ω][A-Za-z0-9_Α-Ωα-ω′'\u0300-\u036f]*",
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
    if token.text.startswith("≡"):
        return 1100
    return {"⊃": 1200, "∨": 1300, "·": 1400, "=": 1450, "∈": 1450}[token.text]


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
    if text.startswith("≡") and text != "≡":
        return "formal_equiv", text[1:]
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


def contains_incomplete_symbol(node: AST) -> bool:
    return node.tag in {"description", "class_incomplete", "relation_incomplete"} or any(
        contains_incomplete_symbol(child) for child in node.children
    )


def relation_binder_variables(text: str) -> str:
    return "x,y" if text == "x̂ŷ" else text


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
            if self.peek() is not None and self.peek().kind == "binary" and self.peek().text == "·":
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
        elif token.kind == "function":
            left = self.application(token)
        elif token.kind == "description_binder":
            condition = self.parenthesized_argument()
            left = AST("description", (condition,), description_variable(token.text))
        elif token.kind == "class_binder":
            condition = self.parenthesized_argument()
            left = AST("class_incomplete", (condition,), "z")
        elif token.kind == "relation_binder":
            condition = self.expression(1500)
            left = AST(
                "relation_incomplete", (condition,), relation_binder_variables(token.text)
            )
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
            close = self.take()
            if close.kind != "rparen":
                raise PMSyntaxError(f"missing closing bracket before offset {close.position}")
            if token.text == "[" and left.tag == "description":
                marker = self.peek()
                if marker is None or marker.kind != "binary" or marker.text != "·":
                    raise PMSyntaxError("a bracketed description must be followed by a scope mark")
                marker = self.take()
                continuation = self.expression(binding_power(marker, "right"))
                continuation = bind_description_occurrences(
                    continuation, left.value or "", left.children[0]
                )
                left = AST("description_scope", (left.children[0], continuation), left.value)
        else:
            raise PMSyntaxError(f"expected proposition at offset {token.position}")

        while (next_token := self.peek()) is not None and next_token.kind == "binary":
            left_bp = binding_power(next_token, "left")
            if left_bp < minimum:
                break
            operator = self.take()
            right_minimum = binding_power(operator, "right")
            # PM later records the unmarked n-ary surface conventions as
            # left-associated (✱2·33 for disjunction, ✱3·02/✱4·34 for
            # products). Implication remains right-associated.
            if operator.right_scope == 0 and operator.text in {"∨", "·"}:
                right_minimum += 1
            right = self.expression(right_minimum)
            tag, value = operator_tag(operator.text)
            if tag == "member" and right.tag == "class_incomplete":
                left = AST("class_membership", (left, right.children[0]), right.value)
            elif tag == "equal" and left.tag == right.tag == "class_incomplete":
                left = AST(
                    "class_extensional_equal", (left.children[0], right.children[0]),
                    f"{left.value},{right.value}",
                )
            elif tag == "equal" and right.tag == "class_incomplete":
                left = AST("class_defined_equal", (left, right.children[0]), right.value)
            elif tag == "equal" and left.tag == "class_incomplete":
                left = AST("class_defined_equal", (right, left.children[0]), left.value)
            elif tag == "equal" and left.tag == right.tag == "relation_incomplete":
                left = AST(
                    "relation_extensional_equal", (left.children[0], right.children[0]),
                    f"{left.value};{right.value}",
                )
            elif tag == "equal" and right.tag == "relation_incomplete":
                left = AST("relation_defined_equal", (left, right.children[0]), right.value)
            elif tag == "equal" and left.tag == "relation_incomplete":
                left = AST("relation_defined_equal", (right, left.children[0]), left.value)
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
        if len(arguments) == 1 and arguments[0].tag == "class_incomplete":
            incomplete = arguments[0]
            continuation = AST(
                application_tag, (AST("class_bound", value=incomplete.value),), function.text
            )
            return AST("class_scope", (incomplete.children[0], continuation), incomplete.value)
        if len(arguments) == 1 and arguments[0].tag == "relation_incomplete":
            incomplete = arguments[0]
            continuation = AST(
                application_tag, (AST("relation_bound", value=incomplete.value),), function.text
            )
            return AST(
                "relation_scope", (incomplete.children[0], continuation), incomplete.value
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
