/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.Dyadic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Data.Nat.Log
public import Mathlib.Data.Rat.Floor

import Mathlib.Algebra.Order.Floor.Semifield

/-!
# Multiplication birthdays of dyadic numbers

The birthday equals the natural ceiling of the absolute value plus the logarithm
of the reduced denominator. Ceiling submultiplicativity and the denominator
product bound then give the birthday multiplication inequality.
-/

public noncomputable section

namespace Dyadic

private theorem abs_toRat_eq (x : Dyadic) :
    |x.toRat| = (x.num.natAbs : ℚ) / x.den := by
  conv_lhs => rw [← Rat.num_div_den x.toRat]
  rw [abs_div, Nat.abs_cast, ← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast]

private theorem den_abs_toRat (x : Dyadic) : |x.toRat|.den = x.den := by
  rcases le_total 0 x.toRat with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_nonpos h, Rat.den_neg_eq_den]

/-- A dyadic birthday is the ceiling of its magnitude plus its denominator exponent. -/
theorem birthday_eq_ceil_abs_add_log_den (x : Dyadic) :
    x.birthday = ⌈|x.toRat|⌉₊ + Nat.log 2 x.den := by
  by_cases hx : x.den = 1
  · rw [birthday_of_den_eq_one hx, abs_toRat_eq, hx]
    simp only [Nat.cast_one, div_one, Nat.ceil_natCast, Nat.log_one_right, add_zero]
  · have hfloor : ⌊|x.toRat|⌋₊ = x.num.natAbs / x.den := by
      rw [abs_toRat_eq, Nat.floor_div_eq_div]
    have hceil : ⌈|x.toRat|⌉₊ = ⌊|x.toRat|⌋₊ + 1 := by
      refine le_antisymm (Nat.ceil_le_floor_add_one _) ?_
      rw [Nat.add_one_le_ceil_iff]
      refine (Nat.floor_le (abs_nonneg _)).lt_of_ne ?_
      intro he
      have hd := congrArg Rat.den he
      rw [Rat.den_natCast, den_abs_toRat] at hd
      exact hx hd.symm
    have hlog : Nat.log 2 x.den = (x.precision.getD 0).toNat := by
      rw [den_eq_two_pow_toNat_precision, Nat.log_pow (by decide)]
    rw [birthday_of_den_ne_one hx, Option.get_eq_getD (fallback := 0), hlog, hceil, hfloor]
    omega

private theorem log_den_mul_le (x y : Dyadic) :
    Nat.log 2 (x * y).den ≤ Nat.log 2 x.den + Nat.log 2 y.den := by
  have hden : (x * y).den ≤ x.den * y.den := by
    apply Nat.le_of_dvd (Nat.mul_pos x.den_pos y.den_pos)
    simpa only [Dyadic.den, Dyadic.coe_mul] using Rat.mul_den_dvd x.toRat y.toRat
  refine (Nat.log_mono_right hden).trans_eq ?_
  rw [den_eq_two_pow_toNat_precision, den_eq_two_pow_toNat_precision,
    ← pow_add, Nat.log_pow (by decide), Nat.log_pow (by decide),
    Nat.log_pow (by decide)]

/-- Dyadic multiplication satisfies the birthday product bound. -/
theorem birthday_mul_le (x y : Dyadic) : (x * y).birthday ≤ x.birthday * y.birthday := by
  by_cases hx : x = 0
  · subst x
    simp [birthday_eq_ceil_abs_add_log_den]
  by_cases hy : y = 0
  · subst y
    simp [birthday_eq_ceil_abs_add_log_den]
  have hceil : ⌈|(x * y).toRat|⌉₊ ≤ ⌈|x.toRat|⌉₊ * ⌈|y.toRat|⌉₊ := by
    rw [Nat.ceil_le, Nat.cast_mul, Dyadic.coe_mul, abs_mul]
    exact mul_le_mul (Nat.le_ceil _) (Nat.le_ceil _) (abs_nonneg _) (by positivity)
  have hxpos : 1 ≤ ⌈|x.toRat|⌉₊ := by
    rw [Nat.one_le_ceil_iff, abs_pos]
    exact fun h ↦ hx (Dyadic.ext (by simpa using h))
  have hypos : 1 ≤ ⌈|y.toRat|⌉₊ := by
    rw [Nat.one_le_ceil_iff, abs_pos]
    exact fun h ↦ hy (Dyadic.ext (by simpa using h))
  have hlog := log_den_mul_le x y
  rw [birthday_eq_ceil_abs_add_log_den, birthday_eq_ceil_abs_add_log_den,
    birthday_eq_ceil_abs_add_log_den]
  nlinarith

end Dyadic
