/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.CoefficientStep

import GonshorBirthday.Surreal.Birthday.DyadicCoefficient
import GonshorBirthday.Surreal.Birthday.Minus

/-!
# Integer and fractional coefficient steps

The negative unit step attains the bound. The half coefficient supplies a
positive source and a strictly smaller step. The successor hypothesis itself
forces finite birthday; no dyadicness premise is passed by these clients.
-/

public noncomputable section

namespace Tests
open Surreal

/-- The negative unit coefficient has a final minus with a zero predecessor. -/
theorem negative_unit_step : (0 : ℝ) - (-1) ≤ 1 := by
  apply real_sub_le_one_of_eq_appendMinus.{0}
  norm_num only [Real.toSurreal_zero, Real.toSurreal_neg, Real.toSurreal_one]
  apply eq_appendMinus_of_birthdayTruncation_eq
  · simp
  · simp
  · norm_num

/-- A fractional positive coefficient also admits the same bound. -/
theorem positive_half_step : (1 : ℝ) - 1 / 2 ≤ 1 := by
  apply real_sub_le_one_of_eq_appendMinus.{0}
  have hh := half_mul_wpow_eq_appendMinuses (0 : Surreal.{0})
  simpa [appendMinuses_one] using hh

/-- A final real minus is dyadic without assuming that the predecessor is dyadic. -/
theorem finite_real_minus {r t : ℝ}
    (h : (r : Surreal.{0}) = appendMinus (t : Surreal.{0})) :
    (r : Surreal.{0}).birthday < NatOrdinal.of Ordinal.omega0 :=
  birthday_real_lt_omega0_of_eq_appendMinus h

end Tests
