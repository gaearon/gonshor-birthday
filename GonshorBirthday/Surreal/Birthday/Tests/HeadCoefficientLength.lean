/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.HeadCoefficientLength
import GonshorBirthday.Surreal.Birthday.Tests.HeadCoefficientCost

/-!
# Exact real-coefficient term birthday clients

A negative doubled reciprocal term after a nondyadic real head adds exactly two
signs to the intrinsic birthday. A zero lower coefficient adds no signs.
-/

universe u
public noncomputable section
open Surreal Set
namespace Tests

/-- A negative coefficient has the same exact two-sign cost after a nondyadic real head. -/
theorem nondyadic_head_negative_double_reciprocal_birthday (r : ℝ)
    (hr : (r : Surreal.{u}).birthday = NatOrdinal.of Ordinal.omega0) :
    ((r : Surreal.{u}) + ((-2 : ℝ) : Surreal) * ω^ (-1 : Surreal)).birthday =
      NatOrdinal.of (Ordinal.omega0 + 2) := by
  have hH : (r : Surreal.{u}).support ⊆ Ioi (-1 : Surreal) := by
    intro v hv
    have hv0 : v = 0 := by
      by_contra hn
      exact mem_support_iff.mp hv (by simp [coeff_realCast, hn])
    rw [hv0]
    exact mem_Ioi.mpr (neg_lt_zero.mpr (zero_lt_one : (0 : Surreal.{u}) < 1))
  have hc : headCoefficientCost (r : Surreal.{u}) (-1) (-2) = 2 := by
    have h := nondyadic_head_double_reciprocal_cost (-r)
      (by simpa only [Real.toSurreal_neg, birthday_neg] using hr)
    rw [Real.toSurreal_neg] at h
    have hn := headCoefficientCost_neg (-(r : Surreal.{u})) (-1) 2
    rw [neg_neg] at hn
    exact hn.trans h
  rw [birthday_head_real_mul_wpow_eq_headCoefficientCost _ _ hH, hc, hr, NatOrdinal.val_of]
  congr 2

/-- A zero coefficient contributes no birthday increment under any higher head. -/
theorem zero_lower_coefficient_keeps_birthday (H s : Surreal.{u})
    (hH : H.support ⊆ Ioi s) :
    (H + ((0 : ℝ) : Surreal) * ω^ s).birthday = H.birthday := by
  rw [birthday_head_real_mul_wpow_eq_headCoefficientCost H s hH,
    headCoefficientCost_zero, NatOrdinal.val_zero, add_zero, NatOrdinal.of_val]

end Tests
