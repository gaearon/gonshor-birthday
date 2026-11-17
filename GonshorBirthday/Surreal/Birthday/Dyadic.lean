/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import CombinatorialGames.Surreal.Birthday.Dyadic

import GonshorBirthday.Surreal.Dyadic
import CombinatorialGames.Surreal.Birthday.Cut
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Rat.Cast.Order

/-!
# Intrinsic birthday of a dyadic surreal

The intrinsic birthday equals the explicit birthday of its canonical dyadic game.
This proves the statement advertised in the pinned CombinatorialGames dependency.
-/

public section

/-- A dyadic surreal has the birthday computed by its canonical dyadic game. -/
theorem Surreal.birthday_dyadic (x : Dyadic) :
    Surreal.birthday x = x.birthday := by
  induction hd : x.den using Nat.strongRec generalizing x with | ind d ih
  subst hd
  obtain hd | hd := eq_or_ne x.den 1
  · have he : (x.num : Surreal) = (x : Surreal) := by
      exact_mod_cast Dyadic.intCast_num_eq_self_of_den_eq_one hd
    rw [← he, Surreal.birthday_intCast, Dyadic.birthday_of_den_eq_one hd]
  · apply le_antisymm
    · rw [← Surreal.mk_dyadic, ← IGame.birthday_dyadic]
      exact Surreal.birthday_mk_le _
    · have hl : Surreal.birthday (x.lower : Surreal) < Surreal.birthday (x : Surreal) := by
        have he : ¬ (x : IGame) ≈ (x.lower : IGame) := by
          rw [← Surreal.mk_eq_mk, Surreal.mk_dyadic, Surreal.mk_dyadic]
          have hxl : (x.lower : Surreal) < (x : Surreal) := by exact_mod_cast x.lower_lt
          exact hxl.ne'
        simpa only [Surreal.mk_dyadic] using (Dyadic.fits_lower hd).surrealBirthday_lt he
      have hr : Surreal.birthday (x.upper : Surreal) < Surreal.birthday (x : Surreal) := by
        have he : ¬ (x : IGame) ≈ (x.upper : IGame) := by
          rw [← Surreal.mk_eq_mk, Surreal.mk_dyadic, Surreal.mk_dyadic]
          have hxu : (x : Surreal) < (x.upper : Surreal) := by exact_mod_cast x.lt_upper
          exact hxu.ne
        simpa only [Surreal.mk_dyadic] using (Dyadic.fits_upper hd).surrealBirthday_lt he
      rw [ih _ (x.den_lower_lt hd) _ rfl] at hl
      rw [ih _ (x.den_upper_lt hd) _ rfl] at hr
      rw [← Dyadic.max_birthday_lower_birthday_upper_add_one_of_den_ne_one hd]
      rw [Nat.cast_add, Nat.cast_one, Nat.cast_max]
      exact Order.add_one_le_iff.mpr (max_lt hl hr)
