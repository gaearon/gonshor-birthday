/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.RealMultiplication

import GonshorBirthday.Surreal.Birthday.DyadicMultiplication

/-!
# Real multiplication birthday clients

The finite formula distinguishes denominator complexity from magnitude. The
real interface includes zero and negative inputs, and a rational cancellation
whose noninteger factor is nondyadic.
-/

universe u
public noncomputable section
namespace Tests
open Surreal

example : Dyadic.birthday ((13 : Dyadic) >>> 2) = 6 := rfl

example : Dyadic.birthday ((-1 : Dyadic) >>> 1) = 2 := rfl

example (r : ℝ) :
    ((0 : Surreal.{u}) * (r : Surreal)).birthday ≤
      (0 : Surreal).birthday * (r : Surreal).birthday := by
  simpa only [Real.toSurreal_zero] using birthday_real_mul_le 0 r

/-- Real multiplication permits factors of opposite signs. -/
theorem real_mul_negative (r t : ℝ) :
    ((r : Surreal.{u}) * -(t : Surreal)).birthday ≤
      (r : Surreal).birthday * (t : Surreal).birthday := by
  simpa only [Real.toSurreal_neg, birthday_neg] using birthday_real_mul_le r (-t)

/-- A nondyadic rational can multiply to an integer without any extra hypothesis. -/
theorem third_cancellation :
    (1 : NatOrdinal.{u}) ≤ 3 * (((1 / 3 : ℝ) : Surreal.{u})).birthday := by
  have h := birthday_real_mul_le (3 : ℝ) (1 / 3 : ℝ)
  rw [← Real.toSurreal_mul] at h
  norm_num only [mul_one_div_cancel (by norm_num : (3 : ℝ) ≠ 0),
    Real.toSurreal_one, Real.toSurreal_ofNat, birthday_one, birthday_ofNat] at h
  exact h

end Tests
