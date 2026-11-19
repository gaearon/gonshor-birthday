/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.ReducedCostCofinality

/-!
# Cofinality across a genuine sign limit

At every negative limit ordinal, retained minus positions and their costs are
cofinal at cutoff zero. Appending one plus destroys cost cofinality of the
right prefixes, even though the original transfinite minus family remains.
-/

public noncomputable section

namespace Tests

open Surreal Ordinal

private theorem negative_limit_retained (o : NatOrdinal.{0})
    (ho : Order.IsSuccLimit o.val) :
    ∀ a < (-o.toSurreal).birthday, ∃ y ∈ rightPrefixes (-o.toSurreal),
      a < y.birthday ∧ y ≤ 0 := by
  intro a ha
  rw [birthday_neg, birthday_toSurreal] at ha
  have hb : a + 1 < o := by
    apply NatOrdinal.val.lt_iff_lt.mp
    simpa only [NatOrdinal.val_add_one, Order.succ_eq_add_one] using
      ho.succ_lt (NatOrdinal.val.strictMono ha)
  refine ⟨-(a + 1).toSurreal, ?_, ?_, ?_⟩
  · apply mem_rightPrefixes_iff.mpr
    constructor
    · rw [birthday_neg, birthday_toSurreal, birthdayTruncation_neg,
        birthdayTruncation_toSurreal hb.le]
    · exact neg_lt_neg (NatOrdinal.toSurreal.strictMono hb)
  · rw [birthday_neg, birthday_toSurreal]
    exact lt_add_one a
  · exact neg_nonpos.mpr (NatOrdinal.toSurreal_nonneg _)

/-- All retained-minus costs approach the entire cost at an arbitrary negative limit ordinal. -/
theorem negative_limit_costs_cofinal (o : NatOrdinal.{0})
    (ho : Order.IsSuccLimit o.val) :
    ∀ S < reducedOmegaCost 0 (-o.toSurreal), ∃ y ∈ rightPrefixes (-o.toSurreal),
      y ≤ 0 ∧ S < reducedOmegaCost 0 y := by
  apply retained_rightPrefix_costs_cofinal_of_positions ?_ (negative_limit_retained o ho)
  rw [birthday_neg, birthday_toSurreal]
  exact NatOrdinal.val.lt_iff_lt.mp (by
    simpa only [NatOrdinal.val_zero] using
      (pos_iff_ne_zero.mpr (Ordinal.isSuccLimit_iff.mp ho).1))

/-- A final plus prevents retained right-prefix costs from approaching the whole cost. -/
theorem final_plus_prevents_cost_cofinality (C : Surreal.{0}) (o : NatOrdinal.{0}) :
    ¬ (∀ S < reducedOmegaCost C (appendPlus (-o.toSurreal)),
      ∃ y ∈ rightPrefixes (appendPlus (-o.toSurreal)),
        y ≤ C ∧ S < reducedOmegaCost C y) := by
  intro h
  have hc := retained_rightPrefixes_cofinal_of_costs_cofinal C (appendPlus (-o.toSurreal)) h
  have hb : (-o.toSurreal).birthday < (appendPlus (-o.toSurreal)).birthday := by
    rw [birthday_appendPlus]
    exact lt_add_one _
  obtain ⟨y, hy, hby, _⟩ := hc (-o.toSurreal).birthday hb
  rw [rightPrefixes_appendPlus] at hy
  exact hby.not_gt (birthday_lt_of_mem_rightPrefixes hy)

end Tests
