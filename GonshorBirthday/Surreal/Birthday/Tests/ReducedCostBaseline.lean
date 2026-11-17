/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.ReducedCostBaseline

import Mathlib.SetTheory.Ordinal.Principal

/-!
# Baseline costs with retained minuses

A minus followed by omega many pluses has baseline cost even when its minus
is retained. Thus the cofinal-retention hypothesis in the no-final-block
theorem cannot be replaced by mere existence of a retained minus.
-/

public noncomputable section

namespace Tests

open Surreal Ordinal

/-- A retained initial minus is absorbed by the final omega-length plus block. -/
theorem baseline_cost_with_retained_minus :
    let x := appendPluses (-1 : Surreal.{0}) Ordinal.omega0
    reducedOmegaCost 0 x = ω^ plusCount x ∧
      ∃ y ∈ rightPrefixes x, y ≤ 0 := by
  dsimp only
  constructor
  · have hp : plusCount (-1 : Surreal.{0}) = 0 := by
      simpa only [NatOrdinal.toSurreal_one] using plusCount_neg_toSurreal (1 : NatOrdinal.{0})
    rw [reducedOmegaCost_appendPluses 0 (-1) Ordinal.omega0_ne_zero,
      reducedOmegaCost_neg_one, ite_eq_left (le_refl (0 : Surreal.{0})),
      plusCount_appendPluses, hp, NatOrdinal.val_zero, zero_add,
      NatOrdinal.val_of, NatOrdinal.val_wpow, NatOrdinal.val_of]
    apply NatOrdinal.val.injective
    change Ordinal.omega0 + Ordinal.omega0 ^ Ordinal.omega0 = Ordinal.omega0 ^ Ordinal.omega0
    apply Ordinal.add_omega0_opow
    simpa only [Ordinal.opow_one] using
      (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).mpr Ordinal.one_lt_omega0
  · refine ⟨0, ?_, le_refl _⟩
    rw [rightPrefixes_appendPluses]
    exact mem_rightPrefixes_iff.mpr ⟨by simp, neg_lt_zero.mpr zero_lt_one⟩

/-- The baseline/cofinal-retention conclusion applies to both possible final signs. -/
theorem cofinal_baseline_excludes_both_final_signs
    (C x z : Surreal.{0}) (a : Ordinal.{0}) (ha : 0 < a)
    (hbase : reducedOmegaCost C x = ω^ plusCount x)
    (hcof : ∀ b < x.birthday, ∃ y ∈ rightPrefixes x, b < y.birthday ∧ y ≤ C) :
    x ≠ appendPluses z a ∧ x ≠ appendMinuses z a :=
  no_final_constant_block_of_baseline_cost hbase hcof z ha

end Tests
