/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.ReducedCostCutoff

import Mathlib.SetTheory.Ordinal.Principal

/-!
# Actual cutoff changes and retained ordinal tails

For the exponent with two minuses, lowering the cutoff from zero to minus one
removes the first expanded block and preserves the second. A lower cutoff
deletes both. This checks the retained boundary in the shared-tail identity.
-/

public noncomputable section

namespace Tests

open Surreal Ordinal

/-- A retained boundary preserves the second omega block after deleting the first. -/
theorem two_minus_cutoff_tail :
    reducedOmegaCost (-1) (appendMinus (-1 : Surreal.{0})) = NatOrdinal.of Ordinal.omega0 := by
  have hy : (-1 : Surreal.{0}) ∈ rightPrefixes (appendMinus (-1)) :=
    mem_rightPrefixes_iff.mpr ⟨birthdayTruncation_appendMinus (-1), appendMinus_lt (-1)⟩
  have hneg : (-1 : Surreal.{0}) ≤ 0 := neg_nonpos.mpr zero_le_one
  have hp : plusCount (-1 : Surreal.{0}) = 0 := by
    simpa only [NatOrdinal.toSurreal_one] using plusCount_neg_toSurreal (1 : NatOrdinal.{0})
  have he := reducedOmegaCost_eq_prefix_add_old_tail hneg hy (le_refl (-1))
  rw [reducedOmegaCost_self_eq_wpow, hp, NatOrdinal.wpow_zero,
    reducedOmegaCost_appendMinus_of_le hneg, reducedOmegaCost_neg_one,
    ite_eq_left (le_refl (0 : Surreal.{0})), hp, zero_add, NatOrdinal.wpow_one,
    NatOrdinal.val_of, NatOrdinal.val_one, Ordinal.add_sub_cancel,
    NatOrdinal.val_of, Ordinal.one_add_omega0] at he
  exact he

/-- Moving below the second minus boundary deletes both minus blocks. -/
theorem two_minus_cutoff_below_boundary (C : Surreal.{0}) (hC : C < -1) :
    reducedOmegaCost C (appendMinus (-1 : Surreal.{0})) = 1 := by
  have hbelow : ∀ y ∈ rightPrefixes (appendMinus (-1 : Surreal.{0})), ¬ y ≤ C := by
    intro y hy hyC
    have hb : y.birthday ≤ (-1 : Surreal.{0}).birthday := by
      have h := birthday_lt_of_mem_rightPrefixes hy
      rw [birthday_appendMinus] at h
      exact Order.lt_add_one_iff.mp h
    have hminus : (-1 : Surreal.{0}) ∈ rightPrefixes (appendMinus (-1)) :=
      mem_rightPrefixes_iff.mpr ⟨birthdayTruncation_appendMinus (-1), appendMinus_lt (-1)⟩
    exact hC.not_ge (rightPrefix_le_cutoff_of_birthday_le hy hyC hminus hb)
  rw [reducedOmegaCost_eq_wpow_of_no_retained_rightPrefixes C _ hbelow,
    plusCount_appendMinus]
  have hp : plusCount (-1 : Surreal.{0}) = 0 := by
    simpa only [NatOrdinal.toSurreal_one] using plusCount_neg_toSurreal (1 : NatOrdinal.{0})
  rw [hp, NatOrdinal.wpow_zero]

end Tests
