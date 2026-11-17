/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.ProductHeadCost

import GonshorBirthday.Surreal.Birthday.ReplacementCost
import GonshorBirthday.Surreal.Birthday.Tests.HeadCost

/-!
# Actual product-head cost clients

The product of two two-term series has a repeated exponent sum. A nondyadic
leading coefficient still deletes the next reciprocal-omega boundary block,
whose reduced cost is exactly one.
-/

universe u
public noncomputable section
open Surreal Set
namespace Tests

/-- A repeated exponent-sum fibre still has the exact one-sign reduced monomial cost. -/
theorem two_term_product_deleted_boundary {τ : ℝ}
    (hτpos : 0 < τ) (hτ : Transcendental ℚ τ) (r : ℝ)
    (hr : (r : Surreal.{u}).birthday = NatOrdinal.of Ordinal.omega0) :
    headOmegaCost
      ((normalFormBirthdayReplacement τ ((r : Surreal.{u}) + ω^ (-1 : Surreal)) *
        normalFormBirthdayReplacement τ (1 + ω^ (-1 : Surreal))).normalFormTrunc (-1))
          (-1) = 1 := by
  have hneg : (-1 : Surreal.{u}) < 0 := neg_lt_zero.mpr zero_lt_one
  have hx : (-1 : Surreal.{u}) ∈ ((r : Surreal.{u}) + ω^ (-1 : Surreal)).support := by
    apply mem_support_iff.mpr
    simp only [coeff_add, Pi.add_apply, coeff_realCast, coeff_wpow,
      Pi.single_eq_of_ne hneg.ne, Pi.single_eq_same, zero_add, ne_eq,
      one_ne_zero, not_false_eq_true]
  have hy : (0 : Surreal.{u}) ∈ (1 + ω^ (-1 : Surreal)).support := by
    apply mem_support_iff.mpr
    simp only [coeff_add, Pi.add_apply, coeff_one, coeff_wpow,
      Pi.single_eq_of_ne hneg.ne', Pi.single_eq_same, add_zero, ne_eq,
      one_ne_zero, not_false_eq_true]
  have htx : ((r : Surreal.{u}) + ω^ (-1 : Surreal)).normalFormTrunc (-1) = r := by
    apply toHahnSeries_inj.mp
    rw [toHahnSeries_trunc, toHahnSeries_add, toHahnSeries_realCast, toHahnSeries_wpow,
      SurrealHahnSeries.trunc_add, SurrealHahnSeries.trunc_single_of_lt hneg,
      SurrealHahnSeries.trunc_single_of_ge le_rfl, add_zero]
  have hty : (1 + ω^ (-1 : Surreal.{u})).normalFormTrunc 0 = 0 := by
    apply toHahnSeries_inj.mp
    rw [toHahnSeries_trunc, toHahnSeries_add, toHahnSeries_one, toHahnSeries_wpow,
      SurrealHahnSeries.trunc_add, SurrealHahnSeries.trunc_single_of_ge le_rfl,
      SurrealHahnSeries.trunc_single_of_ge hneg.le, zero_add, toHahnSeries_zero]
  apply le_antisymm _ (one_le_headOmegaCost _ _)
  have h := headOmegaCost_mul_replacement_le hτpos hτ _ _ hx hy
  rw [headOmegaCost_trunc_normalFormBirthdayReplacement hτpos hτ,
    headOmegaCost_trunc_normalFormBirthdayReplacement hτpos hτ,
    htx, hty, nondyadic_real_reciprocal_head_cost r hr, headOmegaCost_zero,
    wpow_zero, birthday_one, mul_one, add_zero] at h
  exact h

end Tests
