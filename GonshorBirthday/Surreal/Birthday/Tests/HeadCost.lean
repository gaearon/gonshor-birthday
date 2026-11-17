/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import GonshorBirthday.Surreal.Birthday.HeadCost

import GonshorBirthday.Surreal.Birthday.ReducedCostBlocks

/-!
# Native head-cost clients

A nondyadic real deletes the reciprocal-omega minus block, reducing its cost
from omega to one. This separates boundary dyadicness from support alone.
-/

universe u
public noncomputable section
open Surreal Set
namespace Tests

/-- A nondyadic real head deletes the entire reciprocal-omega minus block. -/
theorem nondyadic_real_reciprocal_head_cost (r : ℝ)
    (hr : (r : Surreal.{u}).birthday = NatOrdinal.of Ordinal.omega0) :
    headOmegaCost (r : Surreal.{u}) (-1) = 1 := by
  have hdel : ∀ w ∈ rightPrefixes (-1 : Surreal.{u}),
      ¬ ((r : Surreal).support ⊆ Ici w ∧
        ((r : Surreal).coeff w : Surreal.{u}).birthday < NatOrdinal.of Ordinal.omega0) := by
    intro w hw
    have hb := birthday_lt_of_mem_rightPrefixes hw
    rw [birthday_neg, birthday_one] at hb
    have hbw : w.birthday ≤ 0 := Order.lt_add_one_iff.mp (by simpa only [zero_add] using hb)
    have hw0 : w = 0 := birthday_eq_zero.mp (le_antisymm hbw zero_le)
    rw [hw0, coeff_realCast, Pi.single_eq_same, hr]
    exact fun h ↦ h.2.false
  have hp : plusCount (-1 : Surreal.{u}) = 0 := by
    simpa only [NatOrdinal.toSurreal_one] using plusCount_neg_toSurreal (1 : NatOrdinal.{u})
  rw [headOmegaCost_eq_wpow_of_no_retained_rightPrefix _ _ hdel, hp, NatOrdinal.wpow_zero]

/-- Without a head, the reciprocal omega retains its entire omega-length word. -/
theorem reciprocal_empty_head_cost :
    headOmegaCost (0 : Surreal.{u}) (-1) = NatOrdinal.of Ordinal.omega0 := by
  have hp : plusCount (-1 : Surreal.{u}) = 0 := by
    simpa only [NatOrdinal.toSurreal_one] using plusCount_neg_toSurreal (1 : NatOrdinal.{u})
  rw [headOmegaCost_zero, birthday_wpow_eq_omegaExpansionLength,
    omegaExpansionLength_univ_eq_of_plusCount_zero hp, birthday_neg, birthday_one,
    NatOrdinal.val_one, mul_one, Ordinal.one_add_omega0]

end Tests
