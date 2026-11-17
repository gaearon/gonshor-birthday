/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import CombinatorialGames.NatOrdinal.Pow

import GonshorBirthday.NatOrdinal.ProductSum
import Mathlib.SetTheory.Ordinal.Principal

/-! # Transfer of completed prefix budgets through natural multiplication -/

universe u

public noncomputable section

namespace NatOrdinal

open Ordinal

/-- A prefix, its next block, and a remaining plus power fit the corresponding product budget. -/
theorem oadd_wpow_budget_le_mul {S X Y α p q ρ h : NatOrdinal.{u}}
    (hX : of (S.val + (ω^ (α + 1)).val + if α < p then (ω^ p).val else 0) ≤ X)
    (hY : ω^ q ≤ Y) (hα : α ≤ p) (hρ : ρ ≤ α + q) (hh : h ≤ p + q) :
    of ((S * Y).val + (ω^ (ρ + 1)).val + if ρ < h then (ω^ h).val else 0) ≤ X * Y := by
  have hm : ω^ (α + q + 1) ≤ ω^ (α + 1) * Y := by
    have h := mul_le_mul' (le_refl (ω^ (α + 1))) hY
    rwa [← wpow_add, add_right_comm α 1 q] at h
  by_cases hαp : α < p
  · rw [ite_eq_left hαp] at hX
    have hb := (of_oadd_oadd_mul_le S (ω^ (α + 1)) (ω^ p) Y).trans
      (mul_le_mul' hX le_rfl)
    apply le_trans ?_ hb
    apply of.monotone
    apply add_le_add
    · apply add_le_add le_rfl
      exact val.monotone ((wpow_le_wpow.mpr (add_le_add hρ le_rfl)).trans hm)
    · have hp : ω^ h ≤ ω^ p * Y := by
        calc
          ω^ h ≤ ω^ (p + q) := wpow_le_wpow.mpr hh
          _ = ω^ p * ω^ q := wpow_add _ _
          _ ≤ _ := mul_le_mul' le_rfl hY
      split_ifs
      · exact val.monotone hp
      · exact bot_le
  · have hap : α = p := le_antisymm hα (le_of_not_gt hαp)
    subst p
    rw [ite_eq_right (lt_irrefl α), add_zero] at hX
    have hb := (of_oadd_mul_le S (ω^ (α + 1)) Y).trans (mul_le_mul' hX le_rfl)
    apply le_trans ?_ hb
    apply of.monotone
    rw [add_assoc]
    apply add_le_add_right
    apply le_trans ?_ (val.monotone hm)
    split_ifs with hρh
    · exact (Ordinal.isPrincipal_add_omega0_opow _
        (val.strictMono (wpow_lt_wpow.mpr
          (add_lt_add_of_lt_of_le (hρh.trans_le hh) le_rfl)))
        (val.strictMono (wpow_lt_wpow.mpr (hh.trans_lt (lt_add_one _))))).le
    · rw [add_zero]
      exact val.monotone (wpow_le_wpow.mpr (add_le_add hρ le_rfl))

end NatOrdinal
