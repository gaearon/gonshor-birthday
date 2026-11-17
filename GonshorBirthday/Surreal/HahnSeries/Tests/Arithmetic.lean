/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.HahnSeries.NormalFormMul

/-!
# Public clients of normal-form arithmetic

The product `(ω+1)(ω-1)` has cancelling middle terms and a surviving constant term.
It distinguishes convolution from multiplication of leading terms alone.
-/

public noncomputable section

namespace Tests

open SurrealHahnSeries

/-- Normal forms retain the lower coefficient in a sum. -/
theorem normalForm_add_constantCoeff :
    (Surreal.toHahnSeries (ω^ (1 : Surreal) + 1)).coeff 0 = 1 := by
  simp only [Surreal.toHahnSeries_add, Surreal.toHahnSeries_wpow,
    Surreal.toHahnSeries_one, coeff_add, Pi.add_apply, coeff_single_self, add_eq_right]
  exact coeff_single_of_ne one_ne_zero 1

/-- Convolution preserves the constant term and cancels the two middle terms. -/
theorem normalForm_differenceOfSquares :
    (((ω^ (1 : Surreal) + 1) * (ω^ (1 : Surreal) - 1)).toHahnSeries) =
      single 2 1 - single 0 1 := by
  rw [← Surreal.toHahnSeriesRingEquiv_apply]
  rw [map_mul, map_add, map_sub]
  simp only [Surreal.toHahnSeriesRingEquiv_apply, Surreal.toHahnSeries_wpow,
    Surreal.toHahnSeries_one]
  calc
    (single 1 1 + single 0 1) * (single 1 1 - single 0 1) =
        single 1 1 * single 1 1 - single 0 1 * single 0 1 := by ring
    _ = single 2 1 - single 0 1 := by rw [single_mul_single, single_mul_single]; norm_num

/-- The product has a nonzero coefficient below its leading term. -/
theorem normalForm_differenceOfSquares_constantCoeff :
    (((ω^ (1 : Surreal) + 1) * (ω^ (1 : Surreal) - 1)).toHahnSeries).coeff 0 = -1 := by
  rw [normalForm_differenceOfSquares, sub_eq_add_neg, coeff_add, coeff_neg]
  simp

end Tests
