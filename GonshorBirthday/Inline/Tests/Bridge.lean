/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module
public import GonshorBirthday.Inline.Bridge

/-!
# Direct native CG correspondence clients
-/

universe u
public noncomputable section
namespace GonshorBirthday.Inline.Tests

/-- The compact sum of two units has the native value two before quotienting. -/
theorem unit_add_unit :
    Game.toCG.{u} (Game.add.{u} Game.one.{u} Game.one.{u}) = (2 : _root_.IGame.{u}) := by
  rw [Game.toCG_add, Game.toCG_one]
  exact (one_add_one_eq_two : (1 : _root_.IGame.{u}) + 1 = 2)

/-- Recursive compact multiplication maps to native multiplication, including its unit cut. -/
theorem unit_mul_unit :
    Game.toCG.{u} (Game.mul.{u} Game.one.{u} Game.one.{u}) = (1 : _root_.IGame.{u}) := by
  rw [Game.toCG_mul, Game.toCG_one, mul_one]

/-- Every native game, including nonnumeric games, has an exact indexed representative. -/
theorem native_game_round_trip (x : _root_.IGame.{u}) :
    Game.toCG (Game.fromCG x) = x := Game.toCG_fromCG x

/-- Numericity is reflected as well as preserved. -/
theorem numericity_exact (x : Game.{u}) :
    Game.Numeric x ↔ _root_.IGame.Numeric (Game.toCG x) := Game.numeric_iff_toCG x

/-- Every native surreal is attained, with no countability or birthday restriction. -/
theorem native_surreal_round_trip (x : _root_.Surreal.{u}) :
    (Surreal.fromCG x).toCG = x := Surreal.toCG_fromCG x

end GonshorBirthday.Inline.Tests
