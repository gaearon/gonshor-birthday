/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Inline.BirthdayProof
public import GonshorBirthday.Inline.OrdinalProof

import GonshorBirthday.Surreal.Birthday.Multiplication

/-!
# Multiplication birthdays in the visible game construction

The displayed statement is equivalent, in both directions and in every universe,
to the unrestricted intrinsic birthday bound on the native CG surreal numbers.
-/

universe u
public noncomputable section
namespace GonshorBirthday.Inline

/-- The two birthday bounds agree for each pair of numeric representatives. -/
theorem Surreal.birthday_mul_bound_iff (x y : Surreal.{u}) :
    (Game.birthday (Game.mul x.game y.game) ≤
      naturalMul (Game.birthday x.game) (Game.birthday y.game)) ↔
    (x.toCG * y.toCG).birthday ≤ x.toCG.birthday * y.toCG.birthday := by
  let : _root_.IGame.Numeric (Game.toCG x.game) := x.numeric.toCG
  let : _root_.IGame.Numeric (Game.toCG y.game) := y.numeric.toCG
  have hxy : Game.Numeric (Game.mul x.game y.game) :=
    (Game.numeric_iff_toCG _).mpr (by rw [Game.toCG_mul]; infer_instance)
  rw [Game.birthday_eq_toCG _ hxy, Game.birthday_eq_toCG _ x.numeric,
    Game.birthday_eq_toCG _ y.numeric, naturalMul_eq_native,
    NatOrdinal.of_val, NatOrdinal.of_val]
  simp only [Game.toCG_mul, _root_.Surreal.mk_mul, Surreal.toCG_eq]
  change NatOrdinal.val _ ≤ NatOrdinal.val _ ↔ _
  exact NatOrdinal.val.le_iff_le

/-- The visible unrestricted statement and the native CG statement are equivalent. -/
theorem birthday_mul_statement_iff_native :
    (∀ x y : Surreal.{u}, Game.birthday (Game.mul x.game y.game) ≤
      naturalMul (Game.birthday x.game) (Game.birthday y.game)) ↔
    (∀ x y : _root_.Surreal.{u}, (x * y).birthday ≤ x.birthday * y.birthday) := by
  constructor
  · intro h x y
    have hb := (Surreal.birthday_mul_bound_iff (Surreal.fromCG x) (Surreal.fromCG y)).mp
      (h (Surreal.fromCG x) (Surreal.fromCG y))
    simpa only [Surreal.toCG_fromCG] using hb
  · intro h x y
    exact (Surreal.birthday_mul_bound_iff x y).mpr (h x.toCG y.toCG)

/-- The birthday of a product is bounded by the natural product of the input birthdays. -/
theorem birthday_mul_le (x y : Surreal.{u}) :
    Game.birthday (Game.mul x.game y.game) ≤
      naturalMul (Game.birthday x.game) (Game.birthday y.game) :=
  birthday_mul_statement_iff_native.mpr _root_.Surreal.birthday_mul_le x y

end GonshorBirthday.Inline
