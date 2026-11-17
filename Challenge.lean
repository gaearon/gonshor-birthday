/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Copyright (c) 2025 Aaron Liu. All rights reserved.
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Copyright (c) 2025 Yuyang Zhao. All rights reserved.
Copyright (c) 2024 Theodore Hwa. All rights reserved.
Copyright (c) 2019 Mario Carneiro. All rights reserved.
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov, Aaron Liu, Apurva Nakade, Fox Thomson, František Silváši,
Isabel Longbottom, Junyan Xu, Kim Morrison, Mario Carneiro, Reid Barton, Theodore Hwa,
Violeta Hernández Palacios, Yuyang Zhao
-/
/-
Adapted and modified from the Apache-2.0-licensed CombinatorialGames construction:
https://github.com/vihdzp/combinatorial-games
-/
module

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

namespace GonshorBirthday.Inline

/-- A well-founded Conway game, built from small left and right option families. -/
inductive Game : Type (u + 1) where
  | mk (Left Right : Type u) (left : Left → Game) (right : Right → Game)

namespace Game

/-- A direct move selects either a left or a right option. -/
inductive Move : Game → Game → Prop
  | left {Left Right : Type u} {left : Left → Game} {right : Right → Game}
      (i : Left) : Move (left i) (.mk Left Right left right)
  | right {Left Right : Type u} {left : Left → Game} {right : Right → Game}
      (i : Right) : Move (right i) (.mk Left Right left right)

/-- Direct descent through options is well founded. -/
theorem move_wf : WellFounded Move := by
  constructor
  intro x
  induction x with
  | mk Left Right left right ihLeft ihRight =>
      constructor
      intro y hy
      cases hy with
      | left i => exact ihLeft i
      | right i => exact ihRight i

/-- Lexicographic descent through a pair of game trees is well founded. -/
theorem pair_move_wf :
    WellFounded (Prod.Lex (Move : Game.{u} → Game.{u} → Prop) Move) :=
  move_wf.prod_lex move_wf

/-- Well-founded recursion on an ordered pair of games. -/
noncomputable def pairRec {C : Game → Game → Sort*}
    (step : ∀ x y,
      (∀ x' y', Prod.Lex Move Move (x', y') (x, y) → C x' y') → C x y)
    (x y : Game) : C x y :=
  @WellFounded.fix (Game × Game) (fun p ↦ C p.1 p.2) _ pair_move_wf
    (fun p rec ↦ step p.1 p.2 (fun x' y' h ↦ rec (x', y') h)) (x, y)

/-- Negation interchanges the players and negates every option. -/
@[expose] def neg : Game → Game
  | .mk Left Right left right =>
      .mk Right Left (fun i ↦ neg (right i)) (fun i ↦ neg (left i))

/-- Conway addition: either player moves in exactly one summand. -/
@[expose] noncomputable def add : Game → Game → Game :=
  pairRec fun x y rec ↦
    match x, y with
    | .mk Lx Rx lx rx, .mk Ly Ry ly ry =>
        let x := Game.mk Lx Rx lx rx
        let y := Game.mk Ly Ry ly ry
        .mk (Lx ⊕ Ly) (Rx ⊕ Ry)
          (Sum.elim
            (fun i ↦ rec (lx i) y (Prod.Lex.left y y (Move.left i)))
            (fun j ↦ rec x (ly j) (Prod.Lex.right x (Move.left j))))
          (Sum.elim
            (fun i ↦ rec (rx i) y (Prod.Lex.left y y (Move.right i)))
            (fun j ↦ rec x (ry j) (Prod.Lex.right x (Move.right j))))

/-- Conway multiplication. Its option from options `a` of `x` and `b` of `y` is
`a * y + x * b - a * b`; equal-side moves are left options and opposite-side moves are right
options. -/
@[expose] noncomputable def mul : Game → Game → Game :=
  pairRec fun x y rec ↦
    match x, y with
    | .mk Lx Rx lx rx, .mk Ly Ry ly ry =>
      let x := Game.mk Lx Rx lx rx
      let y := Game.mk Ly Ry ly ry
      let option (a b : Game) (ha : Move a x) (hb : Move b y) :=
        add (add (rec a y (Prod.Lex.left y y ha))
          (rec x b (Prod.Lex.right x hb)))
          (neg (rec a b (Prod.Lex.left b y ha)))
      .mk ((Lx × Ly) ⊕ (Rx × Ry)) ((Lx × Ry) ⊕ (Rx × Ly))
        (Sum.elim
          (fun ij ↦ option (lx ij.1) (ly ij.2) (Move.left ij.1) (Move.left ij.2))
          (fun ij ↦ option (rx ij.1) (ry ij.2) (Move.right ij.1) (Move.right ij.2)))
        (Sum.elim
          (fun ij ↦ option (lx ij.1) (ry ij.2) (Move.left ij.1) (Move.right ij.2))
          (fun ij ↦ option (rx ij.1) (ly ij.2) (Move.right ij.1) (Move.left ij.2)))

/-- Conway's recursive order: `x ≤ y` when no left option of `x` is at least `y`, and no right
option of `y` is at most `x`. -/
@[expose] noncomputable def Le : Game → Game → Prop :=
  Sym2.GameAdd.recursion move_wf fun x y rec ↦
    match x, y with
    | .mk Lx Rx lx rx, .mk Ly Ry ly ry =>
        let x := Game.mk Lx Rx lx rx
        let y := Game.mk Ly Ry ly ry
        (∀ i : Lx, ¬rec y (lx i) (Sym2.GameAdd.snd_fst (Move.left i))) ∧
        (∀ j : Ry, ¬rec (ry j) x (Sym2.GameAdd.fst_snd (Move.right j)))

/-- Conway equivalence, the equality relation on games. -/
def Equivalent (x y : Game) : Prop := Le x y ∧ Le y x

/-- Conway's strict order on numeric games. -/
def Less (x y : Game) : Prop := Le x y ∧ ¬Le y x

/-- A game is numeric when all its options are numeric and every left option is strictly below
every right option. -/
inductive Numeric : Game → Prop where
  | mk {Left Right : Type u} {left : Left → Game} {right : Right → Game} :
      (∀ i j, Less (left i) (right j)) →
      (∀ i, Numeric (left i)) →
      (∀ j, Numeric (right j)) →
      Numeric (.mk Left Right left right)

end Game

/-- A surreal-number representative is a numeric well-founded Conway game. Two representatives
denote the same surreal number precisely when their games are `Game.Equivalent`. -/
structure Surreal : Type (u + 1) where
  game : Game.{u}
  numeric : Game.Numeric game

end GonshorBirthday.Inline

namespace GonshorBirthday.Inline

/-- Lexicographic comparison of ordinal pairs is well founded. -/
theorem ordinal_pair_wf :
    WellFounded (Prod.Lex ((· < ·) : Ordinal.{u} → Ordinal.{u} → Prop)
      ((· < ·) : Ordinal.{u} → Ordinal.{u} → Prop)) :=
  Ordinal.lt_wf.prod_lex Ordinal.lt_wf

/-- Well-founded recursion on an ordered pair of ordinals. -/
def ordinalPairRec {C : Ordinal.{u} → Ordinal.{u} → Sort*}
    (step : ∀ a b,
      (∀ a' b', Prod.Lex (· < ·) (· < ·) (a', b') (a, b) → C a' b') → C a b)
    (a b : Ordinal.{u}) : C a b :=
  @WellFounded.fix (Ordinal.{u} × Ordinal.{u}) (fun p ↦ C p.1 p.2) _
    ordinal_pair_wf
    (fun p rec ↦ step p.1 p.2 (fun a' b' h ↦ rec (a', b') h)) (a, b)

/-- The natural sum is the least ordinal above every sum obtained by lowering one argument. -/
@[expose] def naturalAdd : Ordinal.{u} → Ordinal.{u} → Ordinal.{u} :=
  ordinalPairRec fun a b rec ↦
    max (⨆ x : Set.Iio a, Order.succ (rec x.1 b (Prod.Lex.left b b x.2)))
      (⨆ y : Set.Iio b, Order.succ (rec a y.1 (Prod.Lex.right a y.2)))

/-- Conway's recursive definition of the natural (Hessenberg) product. -/
@[expose] def naturalMul : Ordinal.{u} → Ordinal.{u} → Ordinal.{u} :=
  ordinalPairRec fun a b rec ↦
    sInf {c | ∀ a' (ha : a' < a), ∀ b' (hb : b' < b),
      naturalAdd (rec a' b (Prod.Lex.left b b ha)) (rec a b' (Prod.Lex.right a hb)) <
        naturalAdd c (rec a' b' (Prod.Lex.left b' b ha))}

end GonshorBirthday.Inline

namespace GonshorBirthday.Inline.Game

/-- The construction rank of a game tree. -/
@[expose] def rank : Game.{u} → Ordinal.{u} :=
  Game.rec fun Left Right _ _ ihLeft ihRight ↦
    max (⨆ i : Left, Order.succ (ihLeft i)) (⨆ j : Right, Order.succ (ihRight j))

/-- The intrinsic surreal birthday, minimizing over equivalent numeric games. -/
def birthday (x : Game.{u}) : Ordinal.{u} :=
  sInf (rank '' {y | Numeric y ∧ Equivalent x y})

end GonshorBirthday.Inline.Game

namespace GonshorBirthday.Palomar

/-- warning: declaration uses `sorry` -/
#guard_msgs in
set_option warningAsError false in
/-- The birthday of a product is bounded by the natural product of its birthdays. -/
theorem birthday_mul_le (x y : Inline.Surreal.{u}) :
    Inline.Game.birthday (Inline.Game.mul x.game y.game) ≤
      Inline.naturalMul (Inline.Game.birthday x.game) (Inline.Game.birthday y.game) := by
  sorry

end GonshorBirthday.Palomar
