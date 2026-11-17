/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.HeadCoefficientCost

import GonshorBirthday.Surreal.Birthday.Tests.HeadCost

/-!
# Complete term-cost clients

After a nondyadic real head, twice reciprocal omega costs two signs. Without a
head, the same coefficient and exponent cost omega plus one. A separate zero-sum
client checks cancellation in a finite coefficient fibre.
-/

universe u
public noncomputable section
open Surreal
namespace Tests

private theorem plusCount_neg_one : plusCount (-1 : Surreal.{u}) = 0 := by
  simpa only [NatOrdinal.toSurreal_one] using plusCount_neg_toSurreal (1 : NatOrdinal.{u})

/-- A nondyadic real head leaves only two signs for the doubled reciprocal term. -/
theorem nondyadic_head_double_reciprocal_cost (r : ℝ)
    (hr : (r : Surreal.{u}).birthday = NatOrdinal.of Ordinal.omega0) :
    headCoefficientCost (r : Surreal.{u}) (-1) 2 = 2 := by
  rw [headCoefficientCost_of_ne_zero _ _ (by norm_num),
    nondyadic_real_reciprocal_head_cost r hr, plusCount_neg_one, NatOrdinal.wpow_zero,
    NatOrdinal.val_one, Real.toSurreal_ofNat, birthday_natCast, NatOrdinal.val_natCast,
    one_mul]
  have hsub : ((2 : ℕ) : Ordinal.{u}) - 1 = 1 := by
    simpa only [Nat.reduceSub, Nat.cast_one] using (Ordinal.natCast_sub 2 1).symm
  rw [hsub, NatOrdinal.of_add_one, NatOrdinal.of_one, one_add_one_eq_two]

/-- The doubled reciprocal term has cost omega plus one under the empty head. -/
theorem empty_head_double_reciprocal_cost :
    headCoefficientCost (0 : Surreal.{u}) (-1) 2 =
      NatOrdinal.of (Ordinal.omega0 + 1) := by
  rw [headCoefficientCost_of_ne_zero _ _ (by norm_num), reciprocal_empty_head_cost,
    plusCount_neg_one, NatOrdinal.wpow_zero, NatOrdinal.val_one,
    Real.toSurreal_ofNat, birthday_natCast, NatOrdinal.val_natCast, one_mul, NatOrdinal.val_of]
  have hsub : ((2 : ℕ) : Ordinal.{u}) - 1 = 1 := by
    simpa only [Nat.reduceSub, Nat.cast_one] using (Ordinal.natCast_sub 2 1).symm
  rw [hsub]

/-- A completely cancelled finite fibre contributes no term cost. -/
theorem opposite_coefficients_cancel_cost (H s : Surreal.{u}) (r : ℝ) :
    headCoefficientCost H s ([r, -r] : List ℝ).sum = 0 := by
  simp only [List.sum_cons, List.sum_nil, add_zero, add_neg_cancel, headCoefficientCost_zero]

end Tests
