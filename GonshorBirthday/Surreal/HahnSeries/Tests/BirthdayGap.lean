/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.HahnSeries.BirthdayGap

/-!
# Clients for normal-form birthday gap bounds

For any monomial, every younger surreal stays farther away than every finite multiple of each
strictly smaller monomial. This includes arbitrary exponents and birthdays. At the monomial's
own scale the strict inequality fails already for the younger surreal zero.
-/

universe u

public noncomputable section

namespace Tests

open Surreal Set

/-- The gap estimate applies to every monomial and every younger surreal. -/
theorem monomial_gap {s p w : Surreal.{u}} (hp : p.birthday < (ω^ s).birthday)
    (hw : w < s) (n : ℕ) : n * ω^ w < |p - ω^ s| := by
  apply natCast_mul_wpow_lt_abs_sub_of_birthday_lt _ hp hw n
  simpa only [support_wpow, singleton_subset_iff, mem_Ici] using (le_rfl : s ≤ s)

/-- The scale restriction is strict: zero has exactly monomial-sized distance from a monomial. -/
theorem monomial_gap_boundary (s : Surreal.{u}) :
    (0 : Surreal.{u}).birthday < (ω^ s).birthday ∧
      |(0 : Surreal.{u}) - ω^ s| = ω^ s := by
  constructor
  · rw [birthday_zero]
    exact lt_of_le_of_ne bot_le (fun h ↦ wpow_ne_zero s (birthday_eq_zero.mp h.symm))
  · simp only [zero_sub, abs_neg, wpow_abs]

end Tests
