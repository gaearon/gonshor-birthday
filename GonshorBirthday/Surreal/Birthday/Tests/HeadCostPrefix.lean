/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.HeadCostPrefix

import GonshorBirthday.Surreal.Birthday.Tests.HeadCost

/-!
# Native head-cost recurrence clients

The reciprocal-omega exponent has limit birthday but only its first plus is
retained after the head one. Thus limit continuity must also permit bounded
retained positions, rather than assuming a cofinal retained family.
-/

universe u
public noncomputable section
open Surreal Set
namespace Tests

/-- After the head one, only the first plus of the reciprocal-omega exponent survives. -/
theorem reciprocal_exponent_head_cost :
    headOmegaCost (1 : Surreal.{u}) (ω^ (-1 : Surreal)) = NatOrdinal.of Ordinal.omega0 := by
  have hzero : (0 : Surreal.{u}) ∈ (1 : Surreal).support := by
    apply mem_support_iff.mpr
    simp only [coeff_one, Pi.single_eq_same, ne_eq, one_ne_zero, not_false_eq_true]
  have hdel : ∀ w ∈ rightPrefixes (ω^ (-1 : Surreal.{u})),
      ¬ ((1 : Surreal).support ⊆ Ici w ∧
        ((1 : Surreal).coeff w : Surreal.{u}).birthday < NatOrdinal.of Ordinal.omega0) := by
    intro w hw hret
    exact ((wpow_pos (-1 : Surreal)).trans (mem_rightPrefixes_iff.mp hw).2).not_ge
      (hret.1 hzero)
  have hp : plusCount (-1 : Surreal.{u}) = 0 := by
    simpa only [NatOrdinal.toSurreal_one] using plusCount_neg_toSurreal (1 : NatOrdinal.{u})
  rw [headOmegaCost_eq_wpow_of_no_retained_rightPrefix _ _ hdel,
    plusCount_wpow, hp, NatOrdinal.wpow_zero, NatOrdinal.wpow_one]

/-- The limit criterion applies even though the retained positions stop at the first sign. -/
theorem reciprocal_exponent_limit_criterion (M : NatOrdinal.{u}) :
    NatOrdinal.of Ordinal.omega0 ≤ M ↔ ∀ a < NatOrdinal.of Ordinal.omega0,
      headOmegaCost (1 : Surreal.{u}) (birthdayTruncation (ω^ (-1 : Surreal)) a) ≤ M := by
  have hb : (ω^ (-1 : Surreal.{u})).birthday = NatOrdinal.of Ordinal.omega0 := by
    rw [← headOmegaCost_zero, reciprocal_empty_head_cost]
  have hh := headOmegaCost_le_iff_of_isSuccLimit (1 : Surreal.{u}) (ω^ (-1 : Surreal))
    (by simpa only [hb, NatOrdinal.val_of] using Ordinal.isSuccLimit_omega0) M
  simpa only [reciprocal_exponent_head_cost, hb] using hh

end Tests
