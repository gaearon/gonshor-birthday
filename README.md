# Gonshor's birthday conjecture

This repository contains a Lean proof of Gonshor's conjecture that

$$
b(xy)\le b(x)\otimes b(y)
$$

for any two surreal numbers $x,y$. Here $b(x)$ is the birthday of $x$, or the length
of its sign sequence, and $\otimes$ is natural (Hessenberg) ordinal multiplication.

Gonshor states the conjecture in *An Introduction to the Theory of Surreal Numbers*
(1986), Chapter 6, p. 96. This [MathOverflow discussion](https://mathoverflow.net/questions/476824/birthday-of-combinatorial-game-product)
has background and Philip Ehrlich's account of the previously known bounds.

## Checking the statement

There are two formulations:

| Formulation | Statement | Proof |
|---|---|---|
| Using CombinatorialGames' surreal numbers | [Upstream conjecture](https://github.com/vihdzp/combinatorial-games/blob/ecb008ed1eef7928eed7150f1597b0f635d2253a/CombinatorialGames/Surreal/Birthday/Basic.lean#L282) | [Multiplication.lean](GonshorBirthday/Surreal/Birthday/Multiplication.lean) |
| Using only Mathlib, with the definitions included | [Challenge.lean](Challenge.lean) | [Solution.lean](Solution.lean) |

The CombinatorialGames formulation is exactly the statement already marked
`proof_wanted` in that library:

```lean
theorem Surreal.birthday_mul_le (x y : Surreal) :
  (x * y).birthday ≤ x.birthday * y.birthday
```

Its surreal numbers, multiplication, and birthday come from CombinatorialGames.
The multiplication on the right is the natural product of ordinals.

The Mathlib-only formulation lets you inspect the definitions without following
imports into CombinatorialGames. It defines Conway games, their arithmetic and
order, numeric games, natural ordinal arithmetic, and birthday in one file.
`Challenge.lean` has one intentional `sorry` for the theorem; `Solution.lean`
supplies its proof. These are also the files used for Palomar.

The [equivalence proof](GonshorBirthday/Inline/Multiplication.lean) connects the two
formulations in both directions. In particular, the Mathlib-only version covers
every surreal number and uses its intrinsic birthday: the least rank of an
equivalent numeric game.

## Reading the proof

The [proof outline](PROOF.md) explains the argument and links to the Lean proofs.
It was written by AI and may contain mistakes. It has not been independently
reviewed by a specialist.

## How this was made and checked

I chose the problem and directed the work. Codex agents wrote the mathematical
arguments, Lean proofs, and explanatory text. This follows my earlier work on
Conway's refinement conjecture.

The formal proof uses only `propext`, `Classical.choice`, and `Quot.sound`.
CI checks the axiom dependencies of the whole library. Comparator checks that
Solution proves the statement in Challenge, including the definitions it uses,
and runs independent kernel checkers on the exported proof.

Sources and further details are in [PALOMAR-PROVENANCE.md](PALOMAR-PROVENANCE.md).

## Build

Install [Elan](https://github.com/leanprover/elan), then run:

```sh
lake exe cache get
scripts/verify.sh
```
