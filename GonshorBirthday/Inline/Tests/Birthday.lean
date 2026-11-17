/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Inline.Multiplication

/-!
# Semantic clients of the visible birthday statement

A noncanonical presentation of zero has positive game-tree rank and intrinsic
birthday zero. Natural multiplication is distinguished from ordinary ordinal
multiplication by multiplying omega by two on the left.
-/

universe u
public noncomputable section
namespace GonshorBirthday.Inline.Tests

/-- A noncanonical numeric game for zero. -/
def zeroWithMoves : Game.{u} :=
  Game.add (Game.one : Game.{u}) (Game.neg (Game.one : Game.{u}))

/-- The noncanonical zero is numeric. -/
theorem zeroWithMoves_numeric : Game.Numeric (zeroWithMoves : Game.{u}) := by
  apply (Game.numeric_iff_toCG _).mpr
  rw [zeroWithMoves, Game.toCG_add, Game.toCG_neg, Game.toCG_one]
  infer_instance

/-- Its chosen game tree has rank two. -/
theorem rank_zeroWithMoves : Game.rank (zeroWithMoves : Game.{u}) = 2 := by
  rw [Game.rank_eq_toCG, zeroWithMoves, Game.toCG_add, Game.toCG_neg, Game.toCG_one,
    _root_.IGame.birthday_add, _root_.IGame.birthday_neg, _root_.IGame.birthday_one,
    NatOrdinal.val_add_one, NatOrdinal.val_one]
  exact one_add_one_eq_two

/-- Its intrinsic birthday is zero, distinguishing the minimum from the raw rank. -/
theorem birthday_zeroWithMoves : Game.birthday (zeroWithMoves : Game.{u}) = 0 := by
  rw [Game.birthday_eq_toCG _ zeroWithMoves_numeric]
  simp only [zeroWithMoves, Game.toCG_add, Game.toCG_neg, Game.toCG_one,
    _root_.Surreal.mk_add, _root_.Surreal.mk_neg, _root_.Surreal.mk_one,
    add_neg_cancel, _root_.Surreal.birthday_zero, NatOrdinal.val_zero]

/-- Natural multiplication by two on the left increases omega. -/
theorem omega_lt_naturalMul_two_omega :
    Ordinal.omega0 < naturalMul 2 Ordinal.omega0 := by
  rw [naturalMul_eq_native]
  apply NatOrdinal.val.strictMono
  change NatOrdinal.of Ordinal.omega0 < (2 : NatOrdinal) * NatOrdinal.of Ordinal.omega0
  simpa only [one_mul] using mul_lt_mul_of_pos_right
    (show (1 : NatOrdinal) < 2 from one_lt_two) (NatOrdinal.of.strictMono Ordinal.omega0_pos)

/-- Every native surreal is represented by the Mathlib-only statement. -/
theorem all_native_inputs_covered (x y : _root_.Surreal.{u}) :
    ∃ a b : Surreal.{u}, a.toCG = x ∧ b.toCG = y :=
  ⟨Surreal.fromCG x, Surreal.fromCG y,
    Surreal.toCG_fromCG x, Surreal.toCG_fromCG y⟩

end GonshorBirthday.Inline.Tests
