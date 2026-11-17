# About the Palomar statement

[comparator.json](comparator.json) selects one theorem for Palomar:
`GonshorBirthday.Palomar.birthday_mul_le`.

## The statement

For any two surreal numbers $x,y$, the theorem asserts

$$
b(xy)\le b(x)\otimes b(y),
$$

where $b$ is birthday and $\otimes$ is natural ordinal multiplication.
Gonshor states this conjecture in *An Introduction to the Theory of Surreal
Numbers* (1986), Chapter 6, p. 96.

[Challenge.lean](Challenge.lean) states it using numeric Conway games as
representatives of surreal numbers. Birthday is the least rank of an equivalent
numeric game. The definitions of games, arithmetic, order, and natural ordinal
operations are included in the file, which imports only Mathlib.

The statement works in every Lean universe, with set-sized families of options.
It includes zero and either sign, with no restriction on birthdays or supports.

## How the formulations agree

The library proves the exact statement marked `proof_wanted` in
CombinatorialGames. The [equivalence proof](GonshorBirthday/Inline/Multiplication.lean)
shows that the Mathlib-only statement is equivalent to that statement in both
directions. Every surreal is represented, and the correspondence preserves
multiplication and intrinsic birthday. It also identifies the displayed ordinal
operation with natural multiplication.

## How the proof was made and checked

I chose the problem, directed the work, and am responsible for this repository.
Codex agents supplied the mathematical arguments and Lean proofs.

I reused normal-form infrastructure and the Mathlib-only game definitions from
my [Conway Refinement project](https://github.com/gaearon/conway-refinement).
Both projects build on CombinatorialGames. The original copyright and licence
notices are retained.

The Challenge contains one intentional `sorry` for the theorem being submitted.
[Solution.lean](Solution.lean) proves the same statement. CI checks the Challenge
against its source definitions and audits all project proofs. Comparator checks
that Challenge and Solution agree and that the proof uses only `propext`,
`Classical.choice`, and `Quot.sound`.

The sources and AI tools are listed in [formalization.yaml](formalization.yaml).
Novelty and priority have not been established. There has been no independent
specialist review.

The repository is licensed under Apache-2.0.
