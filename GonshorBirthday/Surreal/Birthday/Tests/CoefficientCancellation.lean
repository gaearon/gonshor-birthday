/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.CoefficientCancellation

import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Data.Rat.Cast.Lemmas

/-!
# Nondyadic coefficient strictness clients

One third and two thirds have dyadic sum but are not dyadic. Their plus-count
addition is therefore strict after any two higher heads, including heads that
cancel. Opposite coefficients also give strictness when their sum is zero.
-/

universe u
public noncomputable section
namespace Tests
open Surreal Set

private theorem birthday_one_third :
    (((1 / 3 : ℝ) : Surreal.{u})).birthday = NatOrdinal.of Ordinal.omega0 := by
  apply (birthday_real_eq_omega0_iff _).mpr
  rintro ⟨q, hq⟩
  change (q.toRat : ℝ) = 1 / 3 at hq
  have hq' : (q.toRat : ℝ) = Rat.cast (1 / 3 : ℚ) := by
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using hq
  have he : q.toRat = (1 / 3 : ℚ) := (Rat.cast_inj (α := ℝ)).mp hq'
  have hd : q.den = 3 := by simpa using congrArg Rat.den he
  obtain ⟨n, hn⟩ := q.den_mem_powers
  change 2 ^ n = q.den at hn
  rw [hd] at hn
  cases n with
  | zero => norm_num at hn
  | succ n => rw [pow_succ] at hn; omega

/-- Nondyadic coefficients give strict plus-count addition after arbitrary higher heads. -/
theorem thirds_strict_plusCount (A B s : Surreal.{u})
    (hA : A.support ⊆ Ioi s) (hB : B.support ⊆ Ioi s) :
    plusCount ((A + (((1 / 3 : ℝ) : Surreal)) * ω^ s) +
      (B + (((2 / 3 : ℝ) : Surreal)) * ω^ s)) <
      plusCount (A + (((1 / 3 : ℝ) : Surreal)) * ω^ s) +
      plusCount (B + (((2 / 3 : ℝ) : Surreal)) * ω^ s) := by
  exact plusCount_add_lt_of_nondyadic_last_coefficient A B s hA hB _ _ 1
    (by norm_num) birthday_one_third

/-- Cancellation of opposite nondyadic coefficients makes the plus-count bound strict. -/
example : plusCount ((((1 / 3 : ℝ) : Surreal.{u})) + (((-1 / 3 : ℝ) : Surreal))) <
    plusCount (((1 / 3 : ℝ) : Surreal.{u})) + plusCount (((-1 / 3 : ℝ) : Surreal)) := by
  have h := plusCount_add_lt_of_nondyadic_last_coefficient
    (0 : Surreal.{u}) 0 0 (by simp) (by simp) (1 / 3) (-1 / 3) 0
    (by norm_num) birthday_one_third
  simpa only [wpow_zero, mul_one, zero_add] using h

end Tests
