/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.HeadCostComparison

import GonshorBirthday.Surreal.Birthday.HeadCostPrefix
import GonshorBirthday.Surreal.Birthday.Tests.HeadCost

/-!
# Restored-block comparison clients

A nondyadic real deletes the reciprocal minus. Removing the head restores it,
so an initial allowance is necessary; the omega allowance pays its complete prefix.
-/

universe u
public noncomputable section
open Surreal Set
namespace Tests

/-- The complete restored reciprocal minus fits an omega initial allowance. -/
theorem restored_reciprocal_cost_with_allowance (r : ℝ) :
    (headOmegaCost (0 : Surreal.{u}) (-1)).val ≤
      Ordinal.omega0 + (headOmegaCost (r : Surreal) (-1)).val := by
  have h := headOmegaCost_add_le_add_of_restored_prefixes (0 : Surreal.{u})
    (r : Surreal) (-1) 0 Ordinal.omega0 zero_le ?_
  · simpa only [zero_add] using h
  intro w hw _ _
  have hb := birthday_lt_of_mem_rightPrefixes hw
  rw [birthday_neg, birthday_one] at hb
  have hbw : w.birthday ≤ 0 := Order.lt_add_one_iff.mp (by simpa only [zero_add] using hb)
  have hw0 : w = 0 := birthday_eq_zero.mp (le_antisymm hbw zero_le)
  simp only [hw0, headOmegaCost_exponent_zero, plusCount_zero, zero_add,
    NatOrdinal.wpow_one, NatOrdinal.val_one, NatOrdinal.val_of, Ordinal.one_add_omega0,
    le_refl]

/-- At a nondyadic boundary, omitting the allowance would give a false comparison. -/
theorem restored_reciprocal_cost_needs_allowance (r : ℝ)
    (hr : (r : Surreal.{u}).birthday = NatOrdinal.of Ordinal.omega0) :
    ¬ headOmegaCost (0 : Surreal.{u}) (-1) ≤ headOmegaCost (r : Surreal) (-1) := by
  rw [reciprocal_empty_head_cost, nondyadic_real_reciprocal_head_cost r hr]
  apply not_le.mpr
  exact NatOrdinal.val.lt_iff_lt.mp (by simpa only [NatOrdinal.val_one,
    NatOrdinal.val_of] using Ordinal.one_lt_omega0)

end Tests
