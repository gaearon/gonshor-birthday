/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.ReducedCostBudget
public import GonshorBirthday.NatOrdinal.PrefixBudget

import GonshorBirthday.NatOrdinal.ProductSum
import Mathlib.Tactic.NormNum

/-!
# Completed-prefix budget clients

The ordinal client includes later output pluses when the selected input has no later
pluses of its own. The surreal client has a mixed-sign input and a cancelling addition
option, with all cutoffs and canonical-prefix hypotheses checked on the actual type.
-/

public noncomputable section

namespace Tests

open NatOrdinal Ordinal Surreal

/-- The output may have later pluses even when the selected input has no later pluses. -/
theorem no_later_input_plus_budget :
    NatOrdinal.of ((ω^ (2 : NatOrdinal.{0})).val + Ordinal.omega0 +
      (ω^ (2 : NatOrdinal.{0})).val) ≤
      ω^ (1 : NatOrdinal.{0}) * ω^ (2 : NatOrdinal.{0}) := by
  have hX : NatOrdinal.of ((1 : NatOrdinal.{0}).val +
      (ω^ ((0 : NatOrdinal.{0}) + 1)).val +
      if (0 : NatOrdinal.{0}) < 0 then (ω^ (0 : NatOrdinal.{0})).val else 0) ≤
      ω^ (1 : NatOrdinal.{0}) := by
    simp only [val_one, zero_add, wpow_one, val_of, lt_irrefl, ite_false, add_zero,
      Ordinal.one_add_omega0, le_refl]
  have h := NatOrdinal.oadd_wpow_budget_le_mul (S := 1) (X := ω^ (1 : NatOrdinal.{0}))
    (Y := ω^ (2 : NatOrdinal.{0})) (α := 0) (p := 0) (q := 2) (ρ := 0) (h := 2)
    hX le_rfl le_rfl (by simp) (by simp)
  simpa only [one_mul, zero_add, wpow_one, val_of,
    show (0 : NatOrdinal.{0}) < 2 from zero_lt_two, ite_true] using h

/-- A mixed-sign input has a retained output right prefix with a cancelled addition option. -/
theorem mixed_input_completed_budget :
    NatOrdinal.of (1 + Ordinal.omega0 +
      if (0 : NatOrdinal.{0}) < plusCount (appendMinus (1 : Surreal.{0}) + -1)
      then (ω^ plusCount (appendMinus (1 : Surreal.{0}) + -1)).val else 0) ≤
      reducedOmegaCost 1 (appendMinus (1 : Surreal.{0})) * NatOrdinal.of Ordinal.omega0 := by
  have hu : (1 : Surreal.{0}) ∈ rightPrefixes (appendMinus 1) :=
    mem_rightPrefixes_iff.mpr ⟨birthdayTruncation_appendMinus 1, appendMinus_lt 1⟩
  have hv : (0 : Surreal.{0}) ∈ rightPrefixes (appendMinus 1 + -1) := by
    apply mem_rightPrefixes_iff.mpr
    constructor
    · simp only [birthday_zero, birthdayTruncation_zero]
    · simpa only [add_neg_cancel] using
        add_lt_add_of_lt_of_le (appendMinus_lt (1 : Surreal.{0})) (le_refl (-1))
  have hi : reducedOmegaCost (min ((1 : Surreal.{0}) + -1) (1 + 0)) (1 + -1) ≤
      reducedOmegaCost 1 (1 : Surreal.{0}) * reducedOmegaCost 0 (-1) := by
    simpa only [add_neg_cancel, zero_add, add_zero,
      min_eq_left (zero_le_one : (0 : Surreal.{0}) ≤ 1)] using
        reducedOmegaCost_add_self_le (1 : Surreal.{0}) (-1) 1 0
  have h := reducedOmegaCost_rightPrefix_add_budget (A := 1) (B := 0)
    hu le_rfl hv (by simp) hi
  simpa only [reducedOmegaCost_zero, plusCount_zero, zero_add, wpow_one, val_of, val_one,
    reducedOmegaCost_neg_one, le_refl, ite_true] using h

end Tests
