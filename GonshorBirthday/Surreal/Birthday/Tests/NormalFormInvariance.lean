/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.NormalFormInvariance

import GonshorBirthday.Surreal.HahnSeries.NormalFormAdd

/-!
# Whole coefficient-birthday invariance clients

Changing only the real head's sign preserves the birthday of a series with a
fixed reciprocal-omega tail. The empty normal form is included in the whole
replacement equality.
-/

universe u
public noncomputable section
namespace Tests
open Surreal

/-- Negating only the real head preserves the whole two-term birthday. -/
theorem head_sign_change_preserves_reciprocal_series_birthday (r : ℝ) :
    ((r : Surreal.{u}) + ω^ (-1 : Surreal)).birthday =
      (((-r : ℝ) : Surreal.{u}) + ω^ (-1 : Surreal)).birthday := by
  apply birthday_eq_of_coeff_birthday_eq
  intro s
  simp only [coeff_add, coeff_realCast, coeff_wpow, Pi.add_apply]
  by_cases hs : s = 0
  · subst s
    have hne : (0 : Surreal.{u}) ≠ -1 := (neg_ne_zero.mpr one_ne_zero).symm
    simp only [Pi.single_eq_same, Pi.single_eq_of_ne hne, add_zero,
      Real.toSurreal_neg, birthday_neg]
  · simp only [Pi.single_eq_of_ne hs, zero_add]

/-- Whole birthday preservation includes the empty normal form. -/
theorem replacement_zero_birthday {τ : ℝ} (hτ : Transcendental ℚ τ) :
    (normalFormBirthdayReplacement τ (0 : Surreal.{u})).birthday = 0 := by
  rw [birthday_normalFormBirthdayReplacement hτ, birthday_zero]

end Tests
