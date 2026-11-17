/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Inline.Basic
public import Mathlib.SetTheory.Ordinal.Arithmetic
public import Mathlib.SetTheory.Ordinal.Family

/-!
# Intrinsic birthdays from game trees

The rank of a game is the least ordinal strictly above the ranks of its options.
For a numeric game, its intrinsic birthday is the least rank of an equivalent
numeric game. Thus different game-tree presentations of one surreal have the
same intrinsic birthday.
-/

universe u
public noncomputable section
namespace GonshorBirthday.Inline.Game

/-- The construction rank of a game tree. -/
@[expose] def rank : Game.{u} → Ordinal.{u} :=
  Game.rec fun Left Right _ _ ihLeft ihRight ↦
    max (⨆ i : Left, Order.succ (ihLeft i)) (⨆ j : Right, Order.succ (ihRight j))

/-- The rank is the least strict upper bound of the option ranks. -/
theorem rank_mk (Left Right : Type u) (left : Left → Game.{u}) (right : Right → Game.{u}) :
    rank (.mk Left Right left right) =
      max (⨆ i : Left, Order.succ (rank (left i)))
        (⨆ j : Right, Order.succ (rank (right j))) := rfl

/-- The intrinsic surreal birthday, minimizing over equivalent numeric games. -/
def birthday (x : Game.{u}) : Ordinal.{u} :=
  sInf (rank '' {y | Numeric y ∧ Equivalent x y})

/-- The defining minimum-rank formula for intrinsic birthday. -/
theorem birthday_eq (x : Game.{u}) :
    birthday x = sInf (rank '' {y | Numeric y ∧ Equivalent x y}) := by rfl

end GonshorBirthday.Inline.Game
