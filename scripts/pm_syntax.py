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


OPERATORS = {"∨": "or", "⊃": "implies", "≡": "equiv"}


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
        if char in ".:":
            end = index + 1
            while end < len(source) and source[end] in ".:":
                end += 1
            text = source[index:end]
            result.append(Token("mark", text, index, mark_count(text), mark_count(text)))
            index = end
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
        if char in ")]}" :
            result.append(Token("rparen", char, index))
            index += 1
            continue
        match = re.match(r"[A-Za-zΑ-Ωα-ω][A-Za-z0-9_Α-Ωα-ω′']*", source[index:])
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
    return {"≡": 1100, "⊃": 1200, "∨": 1300, "·": 1400}[token.text]


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
        return AST("assert", (expression,)) if asserted else expression

    def expression(self, minimum: int) -> AST:
        token = self.take()
        if token.kind == "atom":
            left = AST("atom", value=token.text)
        elif token.kind == "neg":
            left = AST("not", (self.expression(1500),))
        elif token.kind == "lparen":
            left = self.expression(0)
            close = self.take()
            if close.kind != "rparen":
                raise PMSyntaxError(f"missing closing bracket before offset {close.position}")
        else:
            raise PMSyntaxError(f"expected proposition at offset {token.position}")

        while (next_token := self.peek()) is not None and next_token.kind == "binary":
            left_bp = binding_power(next_token, "left")
            if left_bp < minimum:
                break
            operator = self.take()
            right = self.expression(binding_power(operator, "right"))
            left = AST(OPERATORS.get(operator.text, "and"), (left, right))
        return left


def parse(source: str) -> AST:
    return Parser(source).parse()


def main(arguments: list[str] | None = None) -> None:
    import argparse
    cli = argparse.ArgumentParser()
    cli.add_argument("formula")
    options = cli.parse_args(arguments)
    print(json.dumps(parse(options.formula).to_dict(), ensure_ascii=False, sort_keys=True))


if __name__ == "__main__":
    main()
