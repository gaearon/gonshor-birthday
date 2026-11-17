#!/usr/bin/env python3
"""Generate or check the Mathlib-only Palomar statement from checked source declarations."""

from pathlib import Path
import argparse
import json
import sys

ROOT = Path(__file__).resolve().parents[1]
NATIVE_STATEMENT = """/-- The birthday of a product is bounded by the natural product of its birthdays. -/
theorem birthday_mul_le (x y : Inline.Surreal.{u}) :
    Inline.Game.birthday (Inline.Game.mul x.game y.game) ≤
      Inline.naturalMul (Inline.Game.birthday x.game) (Inline.Game.birthday y.game)
"""
CONTRACT = {
    "challenge_module": "Challenge",
    "solution_module": "Solution",
    "theorem_names": ["GonshorBirthday.Palomar.birthday_mul_le"],
    "definition_names": [],
    "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"],
    "enable_nanoda": True,
}


def remove_between(text: str, first: str, following: str) -> str:
    """Remove one unused declaration block, retaining the following declaration."""
    if text.count(first) != 1 or text.count(following) != 1:
        raise ValueError(f"source declaration boundary has drifted: {first}")
    start = text.index(first)
    end = text.index(following, start)
    return text[:start] + text[end:]


def namespace_body(text: str, namespace: str) -> str:
    opening = f"namespace {namespace}\n"
    closing = f"end {namespace}\n"
    if text.count(opening) != 1 or text.count(closing) != 1:
        raise ValueError(f"namespace boundaries have drifted: {namespace}")
    start = text.index(opening)
    end = text.index(closing, start) + len(closing)
    return text[start:end]


def statement_source(repo: Path) -> tuple[str, str]:
    base = repo / "GonshorBirthday/Inline"
    basic_source = (base / "Basic.lean").read_text()
    header = basic_source.split("module\n", 1)[0]
    header = header.replace(
        "Released under Apache", "Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.\n"
        "Released under Apache", 1)
    basic = namespace_body(basic_source, "GonshorBirthday.Inline")
    # Only definitions used by the statement and their well-foundedness proof are needed.
    for first, following in [
        ("/-- The characteristic equation for recursion on a pair of games.",
         "/-- Negation interchanges"),
        ("/-- The defining option equation for negation.", "/-- Conway addition:"),
        ("/-- The defining option equation for Conway addition.", "/-- The zero game `"),
        ("/-- The zero game `", "/-- Conway multiplication."),
        ("/-- The defining option equation for Conway multiplication.",
         "/-- Conway's recursive order:"),
        ("/-- The defining option equation for Conway's order.", "/-- Conway equivalence,"),
        ("/-- Conway equivalence unfolds", "/-- Conway's strict order on numeric games."),
        ("/-- Conway's strict order unfolds", "/-- A game is numeric"),
    ]:
        basic = remove_between(basic, first, following)
    ordinal = namespace_body((base / "Ordinal.lean").read_text(), "GonshorBirthday.Inline")
    for first, following in [
        ("/-- The characteristic equation for pair recursion.", "/-- The natural sum is"),
        ("/-- The defining recursion for natural addition.", "/-- Conway's recursive definition"),
        ("/-- The defining recursion for natural multiplication.", "end GonshorBirthday.Inline"),
    ]:
        ordinal = remove_between(ordinal, first, following)
    birthday = namespace_body((base / "Birthday.lean").read_text(), "GonshorBirthday.Inline.Game")
    for first, following in [
        ("/-- The rank is the least strict upper bound", "/-- The intrinsic surreal birthday,"),
        ("/-- The defining minimum-rank formula", "end GonshorBirthday.Inline.Game"),
    ]:
        birthday = remove_between(birthday, first, following)
    return header, "\n".join((basic, ordinal, birthday))


def render(repo: Path, kind: str) -> str:
    header, definitions = statement_source(repo)
    if kind == "Challenge":
        prefix = header + """module

public import Mathlib.Order.GameAdd
public import Mathlib.SetTheory.Ordinal.Arithmetic
public import Mathlib.SetTheory.Ordinal.Family

/-!
# Gonshor's multiplication birthday conjecture

Gonshor conjectured that the birthday of a product is at most the natural product of
the birthdays of its factors. We state this using numeric Conway games, with birthday
defined as the least rank of an equivalent numeric game.

Source: Gonshor, An Introduction to the Theory of Surreal Numbers (1986), Chapter 6, p. 96.
-/

universe u
public noncomputable section

""" + definitions + "\nnamespace GonshorBirthday.Palomar\n\n"
        body = ("/-- warning: declaration uses `sorry` -/\n#guard_msgs in\n"
                "set_option warningAsError false in\n" + NATIVE_STATEMENT.rstrip()
                + " := by\n  sorry\n")
    else:
        prefix = header + """module

public import GonshorBirthday.Inline.Multiplication

/-! # Proof of the Mathlib-only multiplication birthday statement -/

universe u
public noncomputable section
namespace GonshorBirthday.Palomar

"""
        body = NATIVE_STATEMENT.rstrip() + " :=\n  Inline.birthday_mul_le x y\n"
    return prefix + body + "\nend GonshorBirthday.Palomar\n"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--update", action="store_true")
    parser.add_argument("--repo", type=Path, default=ROOT,
                        help="alternative repository root (used by audit probes)")
    args = parser.parse_args()
    repo = args.repo.resolve()
    try:
        if (repo / "scripts/palomar-statement.txt").read_text() != NATIVE_STATEMENT:
            raise ValueError("advertised statement fragment has drifted")
        if json.loads((repo / "comparator.json").read_text()) != CONTRACT:
            raise ValueError("comparator.json differs from the advertised contract")
        for kind in ("Challenge", "Solution"):
            path = repo / f"{kind}.lean"
            expected = render(repo, kind)
            if kind == "Challenge" and (len(expected.encode()) > 100 * 1024
                                        or len(expected.splitlines()) > 1000):
                raise ValueError("Challenge exceeds Palomar's source-size limit")
            if args.update:
                path.write_text(expected)
            elif path.read_text() != expected:
                raise ValueError(f"{path.name} has drifted; regenerate with --update")
    except (OSError, ValueError, json.JSONDecodeError) as error:
        print(f"palomar-challenge: {error}", file=sys.stderr)
        return 1
    print("palomar-challenge: Mathlib-only statement, solution, and comparator contract checked")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
