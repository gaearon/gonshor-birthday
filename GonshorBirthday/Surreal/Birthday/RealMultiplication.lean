/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.Real

import GonshorBirthday.Surreal.Birthday.DyadicMultiplication

/-!
# Multiplication birthdays of real numbers

For embedded real coefficients the intrinsic birthday of a product is at most the
natural product of the input birthdays. The dyadic case follows from the exact
finite birthday formula; a nondyadic input has birthday omega.

This is van den Dries and Ehrlich, *Fields of surreal numbers and exponentiation*,
Lemma 3.3. Zero inputs and both signs are included.
-/

universe u
public noncomputable section

namespace Surreal

/-- Embedded dyadics satisfy the intrinsic birthday product bound. -/
theorem birthday_dyadic_mul_le (x y : Dyadic) :
    ((x : Surreal.{u}) * (y : Surreal)).birthday ≤
      (x : Surreal).birthday * (y : Surreal).birthday := by
  rw [← Rat.cast_mul, ← Dyadic.coe_mul, birthday_dyadic, birthday_dyadic, birthday_dyadic,
    ← Nat.cast_mul, Nat.cast_le]
  exact Dyadic.birthday_mul_le x y

/-- Embedded real numbers satisfy the intrinsic birthday product bound. -/
theorem birthday_real_mul_le (r t : ℝ) :
    ((r : Surreal.{u}) * (t : Surreal)).birthday ≤
      (r : Surreal).birthday * (t : Surreal).birthday := by
  by_cases hr : r = 0
  · subst r
    simp
  by_cases ht : t = 0
  · subst t
    simp
  have hrb : 1 ≤ (r : Surreal.{u}).birthday := by
    rw [Order.one_le_iff_pos, pos_iff_ne_zero, ne_eq, birthday_eq_zero]
    exact fun h ↦ hr (Real.toSurreal_eq_zero_iff.mp h)
  have htb : 1 ≤ (t : Surreal.{u}).birthday := by
    rw [Order.one_le_iff_pos, pos_iff_ne_zero, ne_eq, birthday_eq_zero]
    exact fun h ↦ ht (Real.toSurreal_eq_zero_iff.mp h)
  rcases (birthday_real_le_omega0 r).lt_or_eq with hrfin | hrinf
  · rcases (birthday_real_le_omega0 t).lt_or_eq with htfin | htinf
    · obtain ⟨x, hx⟩ := (birthday_real_lt_omega0_iff r).mp hrfin
      obtain ⟨y, hy⟩ := (birthday_real_lt_omega0_iff t).mp htfin
      subst r t
      simpa only [Real.toSurreal_ratCast] using birthday_dyadic_mul_le x y
    · have hb := birthday_real_le_omega0 (r * t)
      rw [Real.toSurreal_mul] at hb
      apply hb.trans
      rw [htinf]
      exact le_mul_of_one_le_left zero_le hrb
  · have hb := birthday_real_le_omega0 (r * t)
    rw [Real.toSurreal_mul] at hb
    apply hb.trans
    rw [hrinf]
    exact le_mul_of_one_le_right zero_le htb

end Surreal
